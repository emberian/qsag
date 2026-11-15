module
/-
# Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness — Algebraic `Corduroy` Hypertree & `Hem` Opcode Semantics

Constructive, zero-axiom, zero-`Classical.choice` formalization of:
1. **`Corduroy` Algebraic Poseidon2 Hypertree Spec & Threshold Matched-Input Bit-Identity (`corduroy_threshold_matches_standalone`):**
   - `CorduroyParams` (`h = 28, d = 7` -> `4`-bit subtree height, `w = 4, ell1 = 128, targetSum = 192, forsTrees = 33, forsHeight = 6`), width-12 `Goldilocks` `Poseidon2` sponge (`rate = 8, capacity = 4`, 4-limb `Lane4` digest), injective tweakable `CorduroyAdrs` framing, WOTS+C `targetSum` checksum-free counter grinding, and FORS/TSW bottom layer matching `crates/qsag-core/src/corduroy.rs` and `crates/qsag-agg/src/sig.rs`.
   - Standalone signing completeness (`corduroyVerify_corduroySign`) and dealerless `(t, n)` Shamir/SPDZ share-level `Poseidon2` threshold bit-identity (`corduroy_threshold_matches_standalone`).
2. **Constructive `Corduroy` Multi-Target EUF-CMA Witness Extractor (`corduroy_euf_cma_extract`):**
   - Constructive `Type`-valued (`0 Classical.choice`) extractor over `q_sig` signing queries producing an explicit `CorduroyBreak`:
     - `CorduroyBreak.msgHashCollision`: distinct `(R, pk, msg) ≠ (R', pk, msg')` mapping to the same leaf index + message digest;
     - `CorduroyBreak.spongeTweakCollision`: distinct `(adrs1, in1) ≠ (adrs2, in2)` producing the same 4-Goldilocks-limb sponge output along the hypertree, FORS, or WOTS `T_ℓ` compression;
     - `CorduroyBreak.wotsChainPreimage`: explicit WOTS+C chain link inversion `d* < d_honest` via target-sum conservation (`wotsTargetSum_reused_smaller_digit`).
3. **256-column `Hem` opcode and selector semantics:**
   - Bounded limb decomposition, no-wrap digit unpacking, and exact guard/functional-transition
     decomposition for every scheduled opcode.
   - `hemStepTraceValid_iff_stepOp256TableOk` proves equivalence of the selector-explicit
     table and the original 256-column table; it does not extract a native signature.

For both aggregation profiles an accepted active slot extracts a native signature
(`stepOp256TableOk_xmss_extract`, `stepOp256TableOk_corduroy_extract`) and the extracted committee
gives an accepted serialized signer-witness trace (`xmssMachineToExecutionTrace_accepts`,
`corduroyMachineToExecutionTrace_accepts`). Conversely, for the `XmssPoseidon2` profile every
natively accepted signature yields an accepted table (`stepXmssRows_of_verify`, committees with
inactive slots in `stepXmssSlotsRows_of_verify`); the corresponding constructor for the
`CorduroyPoseidon2` profile is not built. The custody geometry above is distinct from the
aggregation geometry (16 layers, 32 FORS trees of height 8); the two must not be identified.
-/

public import Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
import all Qsag.Math.Goldilocks
public import Qsag.Oracle.Poseidon2
import all Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Aggregation.Aggregation
import all Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
import all Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false
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
  unfold lane4Sub lane4ToList allZeroGold
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
  unfold state12Sub lane4Sub Poseidon2State12.toList allZeroGold
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
  | [], cur => ⟨rfl, rfl, rfl, rfl⟩
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
  | [], cur => ⟨rfl, rfl, rfl, rfl⟩
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
  | [], cur, [], _ => rfl
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
  | [], cur, [], _ => rfl
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
  have hLenInit : poseidon2InitialExtConsts.length = 4 := by decide
  have hLenInt  : poseidon2InternalConsts.length = 22 := by decide
  have hLenTerm : poseidon2TerminalExtConsts.length = 4 := by decide
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

/-! ## §1. `Corduroy` Algebraic Poseidon2 Hypertree Spec & Threshold Bit-Identity (`corduroy_threshold_matches_standalone`) -/

/-- Exact 64-bit ASCII domain-separation constants matching `crates/qsag-agg/src/sig.rs`. -/
def corduroyTagPrfWots       : Goldilocks := Goldilocks.ofNat 0x5153414757505246 -- "QSAGWPRF"
def corduroyTagWotsStep      : Goldilocks := Goldilocks.ofNat 0x5153414757535450 -- "QSAGWSTP"
def corduroyTagWotsPk        : Goldilocks := Goldilocks.ofNat 0x5153414757504B31 -- "QSAGWPK1"
def corduroyTagMerkleNode    : Goldilocks := Goldilocks.ofNat 0x515341474D524B4C -- "QSAGMRKL"
def corduroyTagHMsgStateless : Goldilocks := Goldilocks.ofNat 0x515341474853544C -- "QSAGHSTL"
def corduroyTagHMsgDetTree   : Goldilocks := Goldilocks.ofNat 0x5153414748445452 -- "QSAGHDTR"
def corduroyTagForsPrf       : Goldilocks := Goldilocks.ofNat 0x5153414746505246 -- "QSAGFPRF"
def corduroyTagForsLeaf      : Goldilocks := Goldilocks.ofNat 0x51534147464C4546 -- "QSAGFLEF"
def corduroyTagForsNode      : Goldilocks := Goldilocks.ofNat 0x51534147464E4F44 -- "QSAGFNOD"
def corduroyTagForsRoots     : Goldilocks := Goldilocks.ofNat 0x5153414746525453 -- "QSAGFRTS"
def corduroyPoseidon2Iv      : Goldilocks := Goldilocks.ofNat 0x504F53325F474C31 -- "POS2_GL1"

/-- Domain kind of a tweakable `Corduroy` sponge invocation. -/
inductive CorduroyAdrsKind where
  | prfWots
  | wotsStep
  | wotsPk
  | merkleNode
  | hmsgStateless
  | hmsgDetTree
  | forsPrf
  | forsLeaf
  | forsNode
  | forsRoots
  deriving DecidableEq, Repr

def corduroyAdrsDomainTag : CorduroyAdrsKind → Goldilocks
  | .prfWots       => corduroyTagPrfWots
  | .wotsStep      => corduroyTagWotsStep
  | .wotsPk        => corduroyTagWotsPk
  | .merkleNode    => corduroyTagMerkleNode
  | .hmsgStateless => corduroyTagHMsgStateless
  | .hmsgDetTree   => corduroyTagHMsgDetTree
  | .forsPrf       => corduroyTagForsPrf
  | .forsLeaf      => corduroyTagForsLeaf
  | .forsNode      => corduroyTagForsNode
  | .forsRoots     => corduroyTagForsRoots

theorem corduroyAdrsDomainTag_injective {k1 k2 : CorduroyAdrsKind}
    (h : corduroyAdrsDomainTag k1 = corduroyAdrsDomainTag k2) : k1 = k2 := by
  cases k1 <;> cases k2 <;> first | rfl | (exfalso; revert h; decide)

/-- Tweakable address framing `(kind, layer, treeIdx, kpOrNode, chainIdx, stepIdx, counter)`
    for width-12 `Goldilocks` `Poseidon2` calls across `Corduroy`. -/
structure CorduroyAdrs where
  kind     : CorduroyAdrsKind
  layer    : Nat
  treeIdx  : Nat
  kpOrNode : Nat
  chainIdx : Nat
  stepIdx  : Nat
  counter  : Nat
  deriving DecidableEq, Repr

def CorduroyAdrs.inBounds (a : CorduroyAdrs) : Prop :=
  a.layer < 64 ∧
  a.treeIdx < 2 ^ 56 ∧
  a.kpOrNode < 2 ^ 28 ∧
  a.chainIdx < 4096 ∧
  a.stepIdx < 16 ∧
  a.counter < 2 ^ 56

/-- Pack a `CorduroyAdrs` injectively into the 4-element `Lane4` capacity register of width-12 `Poseidon2`. -/
def corduroyEncodeAdrsCap (a : CorduroyAdrs) : Lane4 :=
  let packedCoord :=
    (a.layer % 64) * (2 ^ 44) +
    (a.kpOrNode % (2 ^ 28)) * (2 ^ 16) +
    (a.chainIdx % 4096) * 16 +
    (a.stepIdx % 16)
  ⟨corduroyAdrsDomainTag a.kind,
   Goldilocks.ofNat packedCoord,
   Goldilocks.ofNat (a.treeIdx % (2 ^ 56)),
   Goldilocks.ofNat (a.counter % (2 ^ 56))⟩

private theorem adrsPack_lt_prime {l kp c s : Nat}
    (hl : l < 64) (hkp : kp < 2 ^ 28) (hc : c < 4096) (hs : s < 16) :
    l * 2 ^ 44 + kp * 2 ^ 16 + c * 16 + s < goldilocksPrime := by
  have hP28 : (2 ^ 28 : Nat) = 268435456 := rfl
  have hP16 : (2 ^ 16 : Nat) = 65536 := rfl
  have hP44 : (2 ^ 44 : Nat) = 17592186044416 := rfl
  have hPrime : goldilocksPrime = 18446744069414584321 := rfl
  rw [hP28] at hkp
  rw [hP44, hP16, hPrime]
  omega

private theorem adrsPow56_lt_prime {x : Nat} (hx : x < 2 ^ 56) : x < goldilocksPrime := by
  have hP56 : (2 ^ 56 : Nat) = 72057594037927936 := rfl
  have hPrime : goldilocksPrime = 18446744069414584321 := rfl
  rw [hP56] at hx
  rw [hPrime]
  omega

private theorem adrsPack_inj {l1 kp1 c1 s1 l2 kp2 c2 s2 : Nat}
    (hkp1 : kp1 < 2 ^ 28) (hc1 : c1 < 4096) (hs1 : s1 < 16)
    (hkp2 : kp2 < 2 ^ 28) (hc2 : c2 < 4096) (hs2 : s2 < 16)
    (h : l1 * 2 ^ 44 + kp1 * 2 ^ 16 + c1 * 16 + s1 = l2 * 2 ^ 44 + kp2 * 2 ^ 16 + c2 * 16 + s2) :
    l1 = l2 ∧ kp1 = kp2 ∧ c1 = c2 ∧ s1 = s2 := by
  have hP28 : (2 ^ 28 : Nat) = 268435456 := rfl
  have hP16 : (2 ^ 16 : Nat) = 65536 := rfl
  have hP44 : (2 ^ 44 : Nat) = 17592186044416 := rfl
  rw [hP28] at hkp1 hkp2
  rw [hP44, hP16] at h
  have hl : l1 = l2 := by omega
  subst hl
  have hkp : kp1 = kp2 := by omega
  subst hkp
  have hc : c1 = c2 := by omega
  subst hc
  exact ⟨rfl, rfl, rfl, by omega⟩

theorem corduroyEncodeAdrsCap_injective {a1 a2 : CorduroyAdrs}
    (hb1 : a1.inBounds) (hb2 : a2.inBounds)
    (hEq : corduroyEncodeAdrsCap a1 = corduroyEncodeAdrsCap a2) : a1 = a2 := by
  rcases a1 with ⟨k1, l1, tr1, kp1, c1, s1, ct1⟩
  rcases a2 with ⟨k2, l2, tr2, kp2, c2, s2, ct2⟩
  rcases hb1 with ⟨hl1, htr1, hkp1, hc1, hs1, hct1⟩
  rcases hb2 with ⟨hl2, htr2, hkp2, hc2, hs2, hct2⟩
  dsimp only at *
  unfold corduroyEncodeAdrsCap at hEq
  simp only [Lane4.mk.injEq] at hEq
  rcases hEq with ⟨hKind, hPack, hTr, hCt⟩
  have hkEq := corduroyAdrsDomainTag_injective hKind
  rw [Nat.mod_eq_of_lt hl1, Nat.mod_eq_of_lt hkp1, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hs1,
      Nat.mod_eq_of_lt hl2, Nat.mod_eq_of_lt hkp2, Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hs2] at hPack
  rw [Nat.mod_eq_of_lt htr1, Nat.mod_eq_of_lt htr2] at hTr
  rw [Nat.mod_eq_of_lt hct1, Nat.mod_eq_of_lt hct2] at hCt
  have hp1Lt := adrsPack_lt_prime hl1 hkp1 hc1 hs1
  have hp2Lt := adrsPack_lt_prime hl2 hkp2 hc2 hs2
  have hPackVal : l1 * 2 ^ 44 + kp1 * 2 ^ 16 + c1 * 16 + s1 =
      l2 * 2 ^ 44 + kp2 * 2 ^ 16 + c2 * 16 + s2 := by
    have hv := congrArg Goldilocks.val hPack
    simpa only [Goldilocks.ofNat, Nat.mod_eq_of_lt hp1Lt, Nat.mod_eq_of_lt hp2Lt] using hv
  obtain ⟨hlEq, hkpEq, hcEq, hsEq⟩ := adrsPack_inj hkp1 hc1 hs1 hkp2 hc2 hs2 hPackVal
  have hTr1Lt := adrsPow56_lt_prime htr1
  have hTr2Lt := adrsPow56_lt_prime htr2
  have hTrVal : tr1 = tr2 := by
    have hv := congrArg Goldilocks.val hTr
    simpa only [Goldilocks.ofNat, Nat.mod_eq_of_lt hTr1Lt, Nat.mod_eq_of_lt hTr2Lt] using hv
  have hCt1Lt := adrsPow56_lt_prime hct1
  have hCt2Lt := adrsPow56_lt_prime hct2
  have hCtVal : ct1 = ct2 := by
    have hv := congrArg Goldilocks.val hCt
    simpa only [Goldilocks.ofNat, Nat.mod_eq_of_lt hCt1Lt, Nat.mod_eq_of_lt hCt2Lt] using hv
  subst hkEq hlEq hTrVal hkpEq hcEq hsEq hCtVal
  rfl

-- Seal 64-bit domain constants and bit-packing so WHNF never reduces 64-bit `Goldilocks.ofNat` literals over symbolic terms.
attribute [local irreducible] corduroyAdrsDomainTag corduroyPoseidon2Iv corduroyTagHMsgStateless corduroyEncodeAdrsCap

/-- Parameter geometry of the algebraic `Corduroy` Poseidon2 hypertree (`corduroy.rs`). -/
structure CorduroyParams where
  totalHeight   : Nat
  numLayers     : Nat
  subtreeHeight : Nat
  winternitzW   : Nat
  wotsChains    : Nat
  targetSum     : Nat
  forsTrees     : Nat
  forsHeight    : Nat
  maxSigsLog2   : Nat
  stateful      : Bool
  deriving DecidableEq, Repr

/-- Well-formedness of a stateless `Corduroy` parameter set (`w = 4`, `0 < targetSum < 3 * ell1`). -/
@[expose] def CorduroyParams.wellFormed (cfg : CorduroyParams) : Bool :=
  !cfg.stateful &&
  (cfg.winternitzW == 4) &&
  (0 < cfg.wotsChains) &&
  (cfg.wotsChains ≤ 128) &&
  (0 < cfg.targetSum) &&
  (cfg.targetSum < 3 * cfg.wotsChains) &&
  (0 < cfg.numLayers) &&
  (0 < cfg.subtreeHeight) &&
  (cfg.totalHeight == cfg.numLayers * cfg.subtreeHeight) &&
  (cfg.totalHeight ≤ 56) &&
  (0 < cfg.forsTrees) &&
  (cfg.forsTrees ≤ 64) &&
  (0 < cfg.forsHeight) &&
  (cfg.forsHeight ≤ 16)

/-- Canonical `Corduroy` custody geometry (`h = 28, d = 7` -> `4`-bit subtrees, `w = 4, ell1 = 128,
    targetSum = 192, forsTrees = 33, forsHeight = 6, maxSigsLog2 = 12, stateful = false`). -/
def corduroyParams : CorduroyParams where
  totalHeight   := 28
  numLayers     := 7
  subtreeHeight := 4
  winternitzW   := 4
  wotsChains    := 128
  targetSum     := 192
  forsTrees     := 33
  forsHeight    := 6
  maxSigsLog2   := 12
  stateful      := false

/-- Explicit geometry projection. Sharing this record conversion does not identify the
    custody hash framing or its signature format with the aggregation verifier. -/
def CorduroyParams.toAggGeometry (cfg : CorduroyParams) : AggSigGeometry :=
  { profile := if cfg.stateful then .xmssPoseidon2 else .corduroyPoseidon2
    wotsChains := cfg.wotsChains
    targetSum := cfg.targetSum
    numLayers := cfg.numLayers
    subtreeHeight := cfg.subtreeHeight
    forsTrees := cfg.forsTrees
    forsHeight := cfg.forsHeight }

/-- Aggregation's actual geometry, represented without silently changing the custody preset.
    Its 64-bit height exceeds the custody parameter check's 56-bit limit. -/
def aggregationCorduroyParams : CorduroyParams :=
  { totalHeight := 64, numLayers := 16, subtreeHeight := 4, winternitzW := 4,
    wotsChains := 128, targetSum := 192, forsTrees := 32, forsHeight := 8,
    maxSigsLog2 := 12, stateful := false }

theorem aggregationCorduroyParams_projection :
    aggregationCorduroyParams.toAggGeometry = corduroyPoseidon2Geom ∧
    aggregationCorduroyParams.toAggGeometry.wellFormed = true := by
  exact ⟨rfl, by decide⟩

/-- The presets are not interchangeable: custody has 33 FORS trees (aggregation permits at
    most 32, in pairs), while aggregation has 64 total height bits (custody permits 56). -/
theorem tooth_corduroy_presets_not_interchangeable :
    corduroyParams.toAggGeometry.wellFormed = false ∧
    aggregationCorduroyParams.wellFormed = false ∧
    corduroyParams.toAggGeometry ≠ corduroyPoseidon2Geom := by
  exact ⟨by decide, by decide, by decide⟩

/-- Compact kernel-decidable `Corduroy` test geometry (`h = 2, d = 1, h' = 2, ell1 = 2, targetSum = 3, k = 2, a = 1`). -/
def corduroyCompactParams : CorduroyParams where
  totalHeight   := 2
  numLayers     := 1
  subtreeHeight := 2
  winternitzW   := 4
  wotsChains    := 2
  targetSum     := 3
  forsTrees     := 2
  forsHeight    := 1
  maxSigsLog2   := 4
  stateful      := false

theorem corduroyParams_matches_custody_preset :
    corduroyParams.wellFormed = true ∧
    corduroyCompactParams.wellFormed = true ∧
    corduroyParams.totalHeight = 28 ∧
    corduroyParams.numLayers = 7 ∧
    corduroyParams.subtreeHeight = 4 ∧
    corduroyParams.wotsChains = corduroyCustody128Params.ell1 ∧
    corduroyParams.targetSum = corduroyCustody128Params.targetSum ∧
    corduroyParams.forsTrees = corduroyCustody128Params.forsTrees ∧
    corduroyParams.forsHeight = corduroyCustody128Params.forsHeight ∧
    corduroyParams.stateful = corduroyCustody128Params.statefulJorts := by
  unfold corduroyParams corduroyCompactParams CorduroyParams.wellFormed
    corduroyCustody128Params PqHashParams.targetSum
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Abstract width-12 permutation handle preventing equation-generator WHNF expansion of 30-round `poseidon2Perm12`
    inside recursive hypertree/Merkle definitions (`LAW-M1` / structural WHNF discipline), instantiated
    canonically with `corduroyPoseidon2Engine := ⟨poseidon2Perm12⟩`. -/
structure CorduroyPermEngine where
  perm : Poseidon2State12 → Poseidon2State12

/-- Canonical width-12 `Goldilocks` `Poseidon2` engine (`R_F = 8, R_P = 22`). -/
def corduroyPoseidon2Engine : CorduroyPermEngine := ⟨poseidon2Perm12⟩

private theorem corduroyPoseidon2Engine_perm : corduroyPoseidon2Engine.perm = poseidon2Perm12 := by
  unfold corduroyPoseidon2Engine; rfl

attribute [local irreducible] corduroyPoseidon2Engine

/-- Width-12 `Goldilocks` `Poseidon2` rate-8 absorption loop (`2 × Lane4` rate, `1 × Lane4` 256-bit capacity). -/
def corduroyAbsorbBlocks (eng : CorduroyPermEngine) (st : Poseidon2State12) (bs : List Lane4) : Poseidon2State12 :=
  match bs with
  | [] => st
  | [b] =>
    let padOne : Lane4 := ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, corduroyPoseidon2Iv⟩
    eng.perm ⟨lane4Add st.b0 b, lane4Add st.b1 padOne, st.b2⟩
  | b0 :: b1 :: rest =>
    let st' := eng.perm ⟨lane4Add st.b0 b0, lane4Add st.b1 b1, st.b2⟩
    corduroyAbsorbBlocks eng st' rest
  termination_by structural bs

/-- Engine-parametric tweakable width-12 `Poseidon2` sponge evaluation (`capacity = 4`, `digest = 4` Goldilocks limbs):
    - Single-block chain/leaf steps (`.wotsStep`, `.forsLeaf`) execute Jive feed-forward
      `lane4Add (eng.perm ⟨val, pkSeed, cap⟩).b0 val` (`sig.rs:poseidon2_compress12_ff`);
    - Multi-block / tree / `T_ℓ` / `H_msg` calls initialize capacity with `adrs` + length framing,
      absorb all `Lane4` blocks at rate `8`, and domain-squeeze `.b0 : Lane4`. -/
def corduroySpongeEvalWith (eng : CorduroyPermEngine) (pkSeed : Lane4) (adrs : CorduroyAdrs) (blocks : List Lane4) : Lane4 :=
  let cap := corduroyEncodeAdrsCap adrs
  match adrs.kind, blocks with
  | .wotsStep, [val] => lane4Add (eng.perm ⟨val, pkSeed, cap⟩).b0 val
  | .forsLeaf, [val] => lane4Add (eng.perm ⟨val, pkSeed, cap⟩).b0 val
  | _, _ =>
    let lenMeta : Lane4 := ⟨Goldilocks.ofNat blocks.length, corduroyPoseidon2Iv, Goldilocks.zero, Goldilocks.zero⟩
    let initSt := eng.perm ⟨pkSeed, lenMeta, cap⟩
    let absorbed := corduroyAbsorbBlocks eng initSt blocks
    let sqSt := eng.perm ⟨ ⟨Goldilocks.add absorbed.b0.x0 Goldilocks.one,
                            absorbed.b0.x1, absorbed.b0.x2, absorbed.b0.x3⟩,
                          absorbed.b1, absorbed.b2 ⟩
    sqSt.b0

/-- Unified tweakable width-12 `Poseidon2` sponge evaluation instantiated at `poseidon2Perm12`. -/
def corduroySpongeEval (pkSeed : Lane4) (adrs : CorduroyAdrs) (blocks : List Lane4) : Lane4 :=
  corduroySpongeEvalWith corduroyPoseidon2Engine pkSeed adrs blocks

theorem corduroySpongeEvalWith_jive_wots (eng : CorduroyPermEngine) (pkSeed : Lane4) (l tr kp c s : Nat) (val : Lane4) :
    corduroySpongeEvalWith eng pkSeed ⟨.wotsStep, l, tr, kp, c, s, 0⟩ [val] =
      lane4Add (eng.perm ⟨val, pkSeed, corduroyEncodeAdrsCap ⟨.wotsStep, l, tr, kp, c, s, 0⟩⟩).b0 val := by
  unfold corduroySpongeEvalWith; rfl

theorem corduroySpongeEvalWith_jive_fors (eng : CorduroyPermEngine) (pkSeed : Lane4) (lg j idx : Nat) (val : Lane4) :
    corduroySpongeEvalWith eng pkSeed ⟨.forsLeaf, 0, lg, idx, j, 0, 0⟩ [val] =
      lane4Add (eng.perm ⟨val, pkSeed, corduroyEncodeAdrsCap ⟨.forsLeaf, 0, lg, idx, j, 0, 0⟩⟩).b0 val := by
  unfold corduroySpongeEvalWith; rfl

attribute [local irreducible] corduroySpongeEvalWith

/-- `Corduroy` public key `(pkSeed, pkRoot)` in 4-limb `Goldilocks` form (`256` bits each). -/
structure CorduroyPublicKey where
  pkSeed : Lane4
  pkRoot : Lane4
  deriving DecidableEq, Repr

/-- `Corduroy` secret key `(skSeed, skPrf, pkSeed)` in 4-limb `Goldilocks` form. -/
structure CorduroySecretKey where
  skSeed : Lane4
  skPrf  : Lane4
  pkSeed : Lane4
  deriving DecidableEq, Repr

-- Specific tweak address constructors matching `sig.rs` / `corduroy.rs`
def wotsPrfAdrs (layer treeIdx kpIdx chainIdx : Nat) : CorduroyAdrs :=
  ⟨.prfWots, layer, treeIdx, kpIdx, chainIdx, 0, 0⟩

def wotsStepAdrs (layer treeIdx kpIdx chainIdx stepIdx : Nat) : CorduroyAdrs :=
  ⟨.wotsStep, layer, treeIdx, kpIdx, chainIdx, stepIdx, 0⟩

def wotsPkAdrs (layer treeIdx kpIdx : Nat) : CorduroyAdrs :=
  ⟨.wotsPk, layer, treeIdx, kpIdx, 0, 0, 0⟩

def xmssMerkleAdrs (layer treeIdx lvl parentIdx : Nat) : CorduroyAdrs :=
  ⟨.merkleNode, layer, treeIdx, parentIdx, lvl, 0, 0⟩

def forsPrfAdrs (leafGlobalIdx treeJ leafIdx : Nat) : CorduroyAdrs :=
  ⟨.forsPrf, 0, leafGlobalIdx, leafIdx, treeJ, 0, 0⟩

def forsLeafAdrs (leafGlobalIdx treeJ leafIdx : Nat) : CorduroyAdrs :=
  ⟨.forsLeaf, 0, leafGlobalIdx, leafIdx, treeJ, 0, 0⟩

def forsNodeAdrs (leafGlobalIdx treeJ lvl parentIdx : Nat) : CorduroyAdrs :=
  ⟨.forsNode, 0, leafGlobalIdx, parentIdx, treeJ * 32 + lvl, 0, 0⟩

def forsRootsAdrs (leafGlobalIdx : Nat) : CorduroyAdrs :=
  ⟨.forsRoots, 0, leafGlobalIdx, 0, 0, 0, 0⟩

def layerHmsgAdrs (layer treeIdx kpIdx tswCtr : Nat) : CorduroyAdrs :=
  ⟨.hmsgDetTree, layer, treeIdx, kpIdx, 0, 0, tswCtr⟩

def msgHashAdrs : CorduroyAdrs :=
  ⟨.hmsgStateless, 0, 0, 0, 0, 0, 0⟩

/-- Secret WOTS+C chain base (`step = 0`) derived from `skSeed` via width-12 `Poseidon2`. -/
def corduroyWotsSecretWith (eng : CorduroyPermEngine) (sk : CorduroySecretKey) (layer treeIdx kpIdx chainIdx : Nat) : Lane4 :=
  (eng.perm ⟨sk.skSeed, sk.pkSeed, corduroyEncodeAdrsCap (wotsPrfAdrs layer treeIdx kpIdx chainIdx)⟩).b0

def corduroyWotsSecret (sk : CorduroySecretKey) (layer treeIdx kpIdx chainIdx : Nat) : Lane4 :=
  corduroyWotsSecretWith corduroyPoseidon2Engine sk layer treeIdx kpIdx chainIdx

/-- Secret FORS leaf (`step = 0`) derived from `skSeed` via width-12 `Poseidon2`. -/
def corduroyForsSecretWith (eng : CorduroyPermEngine) (sk : CorduroySecretKey) (leafGlobalIdx treeJ leafIdx : Nat) : Lane4 :=
  (eng.perm ⟨sk.skSeed, sk.pkSeed, corduroyEncodeAdrsCap (forsPrfAdrs leafGlobalIdx treeJ leafIdx)⟩).b0

def corduroyForsSecret (sk : CorduroySecretKey) (leafGlobalIdx treeJ leafIdx : Nat) : Lane4 :=
  corduroyForsSecretWith corduroyPoseidon2Engine sk leafGlobalIdx treeJ leafIdx

/-- Message randomizer PRF `R = PRF_msg(skPrf, optRand, msgDigest)` binding all 4 limbs of `optRand` and `msg`. -/
def corduroyPrfMsgWith (eng : CorduroyPermEngine) (sk : CorduroySecretKey) (optRand msg : Lane4) : Lane4 :=
  let cap : Lane4 := ⟨corduroyTagHMsgStateless, Goldilocks.zero, Goldilocks.zero, corduroyPoseidon2Iv⟩
  let st0 := eng.perm ⟨sk.skPrf, optRand, cap⟩
  let st1 := eng.perm ⟨lane4Add st0.b0 msg, st0.b1, st0.b2⟩
  st1.b0

def corduroyPrfMsg (sk : CorduroySecretKey) (optRand msg : Lane4) : Lane4 :=
  corduroyPrfMsgWith corduroyPoseidon2Engine sk optRand msg

/-- Public WOTS+C chain step `F(pkSeed, wotsStepAdrs, val)` via Jive feed-forward `Poseidon2`. -/
def corduroyWotsStepWith (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (layer treeIdx kpIdx chainIdx stepIdx : Nat) (val : Lane4) : Lane4 :=
  corduroySpongeEvalWith eng pkSeed (wotsStepAdrs layer treeIdx kpIdx chainIdx stepIdx) [val]

def corduroyWotsStep (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx stepIdx : Nat) (val : Lane4) : Lane4 :=
  corduroyWotsStepWith corduroyPoseidon2Engine pkSeed layer treeIdx kpIdx chainIdx stepIdx val

theorem corduroyWotsStepWith_eq (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (layer treeIdx kpIdx chainIdx stepIdx : Nat) (val : Lane4) :
    corduroyWotsStepWith eng pkSeed layer treeIdx kpIdx chainIdx stepIdx val =
      corduroySpongeEvalWith eng pkSeed (wotsStepAdrs layer treeIdx kpIdx chainIdx stepIdx) [val] := by
  unfold corduroyWotsStepWith; rfl

theorem corduroyWotsStep_eq (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx stepIdx : Nat) (val : Lane4) :
    corduroyWotsStep pkSeed layer treeIdx kpIdx chainIdx stepIdx val =
      corduroySpongeEval pkSeed (wotsStepAdrs layer treeIdx kpIdx chainIdx stepIdx) [val] := by
  unfold corduroyWotsStep corduroyWotsStepWith corduroySpongeEval; rfl

attribute [local irreducible] corduroyWotsStepWith

/-- Iterate `corduroyWotsStepWith` for `steps` links starting at `startStep`. -/
def corduroyChainIterWith (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (layer treeIdx kpIdx chainIdx startStep steps : Nat) (val : Lane4) : Lane4 :=
  match steps with
  | 0 => val
  | s + 1 =>
    let next := corduroyWotsStepWith eng pkSeed layer treeIdx kpIdx chainIdx startStep val
    corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx (startStep + 1) s next
  termination_by structural steps

def corduroyChainIter (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx startStep steps : Nat) (val : Lane4) : Lane4 :=
  corduroyChainIterWith corduroyPoseidon2Engine pkSeed layer treeIdx kpIdx chainIdx startStep steps val

theorem corduroyChainIterWith_add (eng : CorduroyPermEngine) (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx : Nat)
    (a b startStep : Nat) (val : Lane4) :
    corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx (startStep + a) b
      (corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx startStep a val) =
    corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx startStep (a + b) val := by
  induction a generalizing startStep val with
  | zero =>
    rw [Nat.add_zero, Nat.zero_add]
    rfl
  | succ a ih =>
    dsimp only [corduroyChainIterWith]
    have hShift : startStep + (a + 1) = (startStep + 1) + a := by omega
    have hAdd   : a + 1 + b = (a + b) + 1 := by omega
    rw [hShift, hAdd]
    exact ih (startStep + 1) (corduroyWotsStepWith eng pkSeed layer treeIdx kpIdx chainIdx startStep val)

theorem corduroyChainIter_add (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx : Nat)
    (a b startStep : Nat) (val : Lane4) :
    corduroyChainIter pkSeed layer treeIdx kpIdx chainIdx (startStep + a) b
      (corduroyChainIter pkSeed layer treeIdx kpIdx chainIdx startStep a val) =
    corduroyChainIter pkSeed layer treeIdx kpIdx chainIdx startStep (a + b) val :=
  corduroyChainIterWith_add corduroyPoseidon2Engine pkSeed layer treeIdx kpIdx chainIdx a b startStep val

/-- Compress `ell1` WOTS+C chain peaks into `wotsPk : Lane4` (`T_ℓ`). -/
def corduroyWotsPkCompressWith (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (layer treeIdx kpIdx : Nat) (peaks : List Lane4) : Lane4 :=
  corduroySpongeEvalWith eng pkSeed (wotsPkAdrs layer treeIdx kpIdx) peaks

def corduroyWotsPkCompress (pkSeed : Lane4) (layer treeIdx kpIdx : Nat) (peaks : List Lane4) : Lane4 :=
  corduroyWotsPkCompressWith corduroyPoseidon2Engine pkSeed layer treeIdx kpIdx peaks

/-- 2-to-1 tweakable Merkle parent compression. -/
def corduroyMerkleHashWith (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (adrs : CorduroyAdrs) (left right : Lane4) : Lane4 :=
  corduroySpongeEvalWith eng pkSeed adrs [left, right]

def corduroyMerkleHash (pkSeed : Lane4) (adrs : CorduroyAdrs) (left right : Lane4) : Lane4 :=
  corduroyMerkleHashWith corduroyPoseidon2Engine pkSeed adrs left right

/-- Public FORS 1-step leaf compression (`0 -> 1`). -/
def corduroyForsLeafHashWith (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (leafGlobalIdx treeJ leafIdx : Nat) (secVal : Lane4) : Lane4 :=
  corduroySpongeEvalWith eng pkSeed (forsLeafAdrs leafGlobalIdx treeJ leafIdx) [secVal]

def corduroyForsLeafHash (pkSeed : Lane4) (leafGlobalIdx treeJ leafIdx : Nat) (secVal : Lane4) : Lane4 :=
  corduroyForsLeafHashWith corduroyPoseidon2Engine pkSeed leafGlobalIdx treeJ leafIdx secVal

/-- Compress `k` FORS tree roots into `forsPk : Lane4` (`T_k`). -/
def corduroyForsRootsCompressWith (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (leafGlobalIdx : Nat) (roots : List Lane4) : Lane4 :=
  corduroySpongeEvalWith eng pkSeed (forsRootsAdrs leafGlobalIdx) roots

def corduroyForsRootsCompress (pkSeed : Lane4) (leafGlobalIdx : Nat) (roots : List Lane4) : Lane4 :=
  corduroyForsRootsCompressWith corduroyPoseidon2Engine pkSeed leafGlobalIdx roots

/-- Deterministic hypertree layer message digest `H_msg(pk, layer, treeIdx, kpIdx, tswCtr, childRoot)`. -/
def corduroyLayerHmsgWith (eng : CorduroyPermEngine) (pk : CorduroyPublicKey)
    (layer treeIdx kpIdx tswCtr : Nat) (childRoot : Lane4) : Lane4 :=
  corduroySpongeEvalWith eng pk.pkSeed (layerHmsgAdrs layer treeIdx kpIdx tswCtr) [pk.pkRoot, childRoot]

def corduroyLayerHmsg (pk : CorduroyPublicKey) (layer treeIdx kpIdx tswCtr : Nat) (childRoot : Lane4) : Lane4 :=
  corduroyLayerHmsgWith corduroyPoseidon2Engine pk layer treeIdx kpIdx tswCtr childRoot

/-- Stateless message hash `H_msg(R, pk, msg)` returning `(leafGlobalIdx, forsIndices, msgDigest)`. -/
def corduroyHashMsgWith (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (rRand : Lane4) (pk : CorduroyPublicKey) (msg : Lane4) : Nat × List Nat × Lane4 :=
  let digest := corduroySpongeEvalWith eng pk.pkSeed msgHashAdrs [rRand, pk.pkRoot, msg]
  let leafGlobalIdx := digest.x0.val % (2 ^ (cfg.numLayers * cfg.subtreeHeight))
  let treeMod := 2 ^ cfg.forsHeight
  let forsIndices := (List.range cfg.forsTrees).map fun j =>
    let stepDigest := corduroySpongeEvalWith eng pk.pkSeed ⟨.hmsgStateless, 0, 0, 0, j + 1, 0, 0⟩ [rRand, pk.pkRoot, msg]
    stepDigest.x0.val % treeMod
  (leafGlobalIdx, forsIndices, digest)

def corduroyHashMsg (cfg : CorduroyParams) (rRand : Lane4) (pk : CorduroyPublicKey) (msg : Lane4) :
    Nat × List Nat × Lane4 :=
  corduroyHashMsgWith corduroyPoseidon2Engine cfg rRand pk msg

theorem corduroyHashMsgWith_bounds (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (rRand : Lane4) (pk : CorduroyPublicKey) (msg : Lane4) :
    (corduroyHashMsgWith eng cfg rRand pk msg).1 < 2 ^ (cfg.numLayers * cfg.subtreeHeight) ∧
    (corduroyHashMsgWith eng cfg rRand pk msg).2.1.length = cfg.forsTrees ∧
    ∀ idx ∈ (corduroyHashMsgWith eng cfg rRand pk msg).2.1, idx < 2 ^ cfg.forsHeight := by
  unfold corduroyHashMsgWith
  dsimp only
  refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_, ?_⟩
  · rw [List.length_map, List.length_range]
  · intro idx hMem
    rw [List.mem_map] at hMem
    obtain ⟨_, _, rfl⟩ := hMem
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem corduroyHashMsg_bounds (cfg : CorduroyParams) (rRand : Lane4) (pk : CorduroyPublicKey) (msg : Lane4) :
    (corduroyHashMsg cfg rRand pk msg).1 < 2 ^ (cfg.numLayers * cfg.subtreeHeight) ∧
    (corduroyHashMsg cfg rRand pk msg).2.1.length = cfg.forsTrees ∧
    ∀ idx ∈ (corduroyHashMsg cfg rRand pk msg).2.1, idx < 2 ^ cfg.forsHeight :=
  corduroyHashMsgWith_bounds corduroyPoseidon2Engine cfg rRand pk msg

/-- Extract `n` base-4 digits (`∈ {0, 1, 2, 3}`) from a natural number `v` (least-significant digit first). -/
def extractBase4Nat : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => (v % 4) :: extractBase4Nat n (v / 4)

/-- Reconstruct a natural number from base-4 digits (least-significant digit first). -/
def evalBase4Nat : List Nat → Nat
  | [] => 0
  | d :: rest => d + 4 * evalBase4Nat rest

private theorem mod_four_step_eq (v m : Nat) (hm : 0 < m) :
    v % 4 + 4 * ((v / 4) % m) = v % (m * 4) := by
  let d := v % 4
  let r := (v / 4) % m
  let q := (v / 4) / m
  have hd : d < 4 := Nat.mod_lt v (by decide)
  have hr : r < m := Nat.mod_lt (v / 4) hm
  have hv1 : v = d + 4 * (v / 4) := (Nat.mod_add_div v 4).symm
  have hv2 : v / 4 = r + m * q := (Nat.mod_add_div (v / 4) m).symm
  have hv3 : v = (d + 4 * r) + (m * 4) * q := by
    rw [hv1, hv2, Nat.left_distrib]
    have hMul : 4 * (m * q) = (m * 4) * q := by
      rw [← Nat.mul_assoc, Nat.mul_comm 4 m]
    rw [hMul, ← Nat.add_assoc]
  have hBound : d + 4 * r < m * 4 := by omega
  have hRhs : v % (m * 4) = d + 4 * r := by
    rw [hv3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hBound]
  exact hRhs.symm

theorem extractBase4Nat_spec :
    ∀ (n v : Nat),
      (extractBase4Nat n v).length = n ∧
      (∀ d ∈ extractBase4Nat n v, d < 4) ∧
      evalBase4Nat (extractBase4Nat n v) = v % (4 ^ n)
  | 0, v => by simp [extractBase4Nat, evalBase4Nat, Nat.mod_one]
  | n + 1, v => by
    obtain ⟨hLen, hLt, hEval⟩ := extractBase4Nat_spec n (v / 4)
    refine ⟨by simp [extractBase4Nat, hLen], ?_, ?_⟩
    · intro d hMem
      simp only [extractBase4Nat, List.mem_cons] at hMem
      rcases hMem with rfl | hTail
      · exact Nat.mod_lt v (by decide)
      · exact hLt d hTail
    · simp only [extractBase4Nat, evalBase4Nat, hEval, Nat.pow_succ]
      exact mod_four_step_eq v (4 ^ n) (Nat.pow_pos (by decide))

attribute [local irreducible] extractBase4Nat

private theorem gold_val_lt_four_pow_32 (a : Goldilocks) : a.val < 4 ^ 32 := by
  have hlt := a.isLt
  have hP32 : (4 ^ 32 : Nat) = 18446744073709551616 := rfl
  have hPrime : goldilocksPrime = 18446744069414584321 := rfl
  rw [hPrime] at hlt
  rw [hP32]
  omega

theorem extractBase4Nat_32_injective {a b : Goldilocks}
    (h : extractBase4Nat 32 a.val = extractBase4Nat 32 b.val) : a = b := by
  have haLt := gold_val_lt_four_pow_32 a
  have hbLt := gold_val_lt_four_pow_32 b
  have h1 := (extractBase4Nat_spec 32 a.val).2.2
  have h2 := (extractBase4Nat_spec 32 b.val).2.2
  rw [Nat.mod_eq_of_lt haLt] at h1
  rw [Nat.mod_eq_of_lt hbLt] at h2
  apply Goldilocks.ext
  rw [← h1, ← h2, h]

/-- Extract `ell1` (`≤ 128`) base-4 digits from the 4 `Goldilocks` limbs of `d : Lane4` (`32` digits per limb). -/
def corduroyExtractDigits (ell1 : Nat) (d : Lane4) : List Nat :=
  let all128 :=
    extractBase4Nat 32 d.x0.val ++
    extractBase4Nat 32 d.x1.val ++
    extractBase4Nat 32 d.x2.val ++
    extractBase4Nat 32 d.x3.val
  all128.take ell1

theorem corduroyExtractDigits_spec {ell1 : Nat} (hLe : ell1 ≤ 128) (d : Lane4) :
    (corduroyExtractDigits ell1 d).length = ell1 ∧
    ∀ x ∈ corduroyExtractDigits ell1 d, x < 4 := by
  obtain ⟨l0, b0, _⟩ := extractBase4Nat_spec 32 d.x0.val
  obtain ⟨l1, b1, _⟩ := extractBase4Nat_spec 32 d.x1.val
  obtain ⟨l2, b2, _⟩ := extractBase4Nat_spec 32 d.x2.val
  obtain ⟨l3, b3, _⟩ := extractBase4Nat_spec 32 d.x3.val
  unfold corduroyExtractDigits
  refine ⟨?_, ?_⟩
  · simp only [List.length_take, List.length_append, l0, l1, l2, l3]
    omega
  · intro x hMem
    have hIn := List.mem_of_mem_take hMem
    simp only [List.mem_append] at hIn
    rcases hIn with ((h0 | h1) | h2) | h3
    · exact b0 x h0
    · exact b1 x h1
    · exact b2 x h2
    · exact b3 x h3

private theorem append_inj_of_eq_len {α : Type} :
    ∀ {u1 v1 u2 v2 : List α}, u1.length = u2.length → u1 ++ v1 = u2 ++ v2 → u1 = u2 ∧ v1 = v2
  | [], v1, [], v2, _, h => ⟨rfl, h⟩
  | _ :: _, _, [], _, hL, _ => absurd hL (by simp only [List.length_cons, List.length_nil]; omega)
  | [], _, _ :: _, _, hL, _ => absurd hL (by simp only [List.length_cons, List.length_nil]; omega)
  | a :: u1, v1, b :: u2, v2, hL, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨ih1, ih2⟩ := append_inj_of_eq_len (Nat.succ.inj hL) h.2
    exact ⟨by rw [h.1, ih1], ih2⟩

/-- **128-Digit Bijective Codeword Theorem (`corduroyExtractDigits_128_injective`)**:
    Because every `Goldilocks` limb is `< p < 2^64 = 4^32`, the 128 base-4 digits of `Lane4`
    determine all 4 field elements injectively with zero truncated bits. -/
theorem corduroyExtractDigits_128_injective {d1 d2 : Lane4}
    (h : corduroyExtractDigits 128 d1 = corduroyExtractDigits 128 d2) : d1 = d2 := by
  obtain ⟨l10, _, _⟩ := extractBase4Nat_spec 32 d1.x0.val
  obtain ⟨l11, _, _⟩ := extractBase4Nat_spec 32 d1.x1.val
  obtain ⟨l12, _, _⟩ := extractBase4Nat_spec 32 d1.x2.val
  obtain ⟨l13, _, _⟩ := extractBase4Nat_spec 32 d1.x3.val
  obtain ⟨l20, _, _⟩ := extractBase4Nat_spec 32 d2.x0.val
  obtain ⟨l21, _, _⟩ := extractBase4Nat_spec 32 d2.x1.val
  obtain ⟨l22, _, _⟩ := extractBase4Nat_spec 32 d2.x2.val
  obtain ⟨l23, _, _⟩ := extractBase4Nat_spec 32 d2.x3.val
  unfold corduroyExtractDigits at h
  have hTake1 : (extractBase4Nat 32 d1.x0.val ++ extractBase4Nat 32 d1.x1.val ++
      extractBase4Nat 32 d1.x2.val ++ extractBase4Nat 32 d1.x3.val).length = 128 := by
    simp [l10, l11, l12, l13]
  have hTake2 : (extractBase4Nat 32 d2.x0.val ++ extractBase4Nat 32 d2.x1.val ++
      extractBase4Nat 32 d2.x2.val ++ extractBase4Nat 32 d2.x3.val).length = 128 := by
    simp [l20, l21, l22, l23]
  rw [List.take_of_length_le (Nat.le_of_eq hTake1),
      List.take_of_length_le (Nat.le_of_eq hTake2)] at h
  obtain ⟨h012, h3⟩ := append_inj_of_eq_len (by simp [l10, l11, l12, l20, l21, l22]) h
  obtain ⟨h01, h2⟩  := append_inj_of_eq_len (by simp [l10, l11, l20, l21]) h012
  obtain ⟨h0, h1⟩   := append_inj_of_eq_len (by simp [l10, l20]) h01
  exact Lane4.ext
    (extractBase4Nat_32_injective h0)
    (extractBase4Nat_32_injective h1)
    (extractBase4Nat_32_injective h2)
    (extractBase4Nat_32_injective h3)

/-- Sum of a list of natural numbers (`∑ d_i`). -/
def natListSum : List Nat → Nat
  | [] => 0
  | d :: ds => d + natListSum ds

/-! ### Generic Parametric Merkle Tree Builder & Verifier -/

/-- Compute node `(height, nodeIdx)` of a binary Merkle tree with leaf function `leafFn` and tweak family `mkAdrs`. -/
def computeCorduroyMerkleNodeWith (eng : CorduroyPermEngine) (pkSeed : Lane4) (mkAdrs : Nat → Nat → CorduroyAdrs)
    (leafFn : Nat → Lane4) (height nodeIdx : Nat) : Lane4 :=
  match height with
  | 0 => leafFn nodeIdx
  | h + 1 =>
    let left  := computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn h (2 * nodeIdx)
    let right := computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn h (2 * nodeIdx + 1)
    corduroyMerkleHashWith eng pkSeed (mkAdrs h nodeIdx) left right
  termination_by structural height

def computeCorduroyMerkleNode (pkSeed : Lane4) (mkAdrs : Nat → Nat → CorduroyAdrs)
    (leafFn : Nat → Lane4) (height nodeIdx : Nat) : Lane4 :=
  computeCorduroyMerkleNodeWith corduroyPoseidon2Engine pkSeed mkAdrs leafFn height nodeIdx

/-- Build the bottom-up sibling authentication path of length `rem` for `idx`. -/
def buildCorduroyMerklePathWith (eng : CorduroyPermEngine) (pkSeed : Lane4) (mkAdrs : Nat → Nat → CorduroyAdrs)
    (leafFn : Nat → Lane4) (rem lvl idx : Nat) : List Lane4 :=
  match rem with
  | 0 => []
  | r + 1 =>
    let sibIdx := if idx % 2 == 0 then idx + 1 else idx - 1
    let sib := computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn lvl sibIdx
    sib :: buildCorduroyMerklePathWith eng pkSeed mkAdrs leafFn r (lvl + 1) (idx / 2)
  termination_by structural rem

def buildCorduroyMerklePath (pkSeed : Lane4) (mkAdrs : Nat → Nat → CorduroyAdrs)
    (leafFn : Nat → Lane4) (rem lvl idx : Nat) : List Lane4 :=
  buildCorduroyMerklePathWith corduroyPoseidon2Engine pkSeed mkAdrs leafFn rem lvl idx

/-- Walk a sibling authentication path from `(lvl, idx, cur)` up to the subtree root. -/
def walkCorduroyMerklePathWith (eng : CorduroyPermEngine) (pkSeed : Lane4) (mkAdrs : Nat → Nat → CorduroyAdrs)
    (lvl idx : Nat) (cur : Lane4) (path : List Lane4) : Lane4 :=
  match path with
  | [] => cur
  | sib :: rest =>
    let parentIdx := idx / 2
    let parent :=
      if idx % 2 == 0 then corduroyMerkleHashWith eng pkSeed (mkAdrs lvl parentIdx) cur sib
      else corduroyMerkleHashWith eng pkSeed (mkAdrs lvl parentIdx) sib cur
    walkCorduroyMerklePathWith eng pkSeed mkAdrs (lvl + 1) parentIdx parent rest
  termination_by structural path

def walkCorduroyMerklePath (pkSeed : Lane4) (mkAdrs : Nat → Nat → CorduroyAdrs)
    (lvl idx : Nat) (cur : Lane4) (path : List Lane4) : Lane4 :=
  walkCorduroyMerklePathWith corduroyPoseidon2Engine pkSeed mkAdrs lvl idx cur path

theorem buildCorduroyMerklePathWith_length (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (mkAdrs : Nat → Nat → CorduroyAdrs) (leafFn : Nat → Lane4) :
    ∀ (rem lvl idx : Nat), (buildCorduroyMerklePathWith eng pkSeed mkAdrs leafFn rem lvl idx).length = rem
  | 0, _, _ => rfl
  | rem + 1, lvl, idx => by
    simp [buildCorduroyMerklePathWith, buildCorduroyMerklePathWith_length eng pkSeed mkAdrs leafFn rem (lvl + 1) (idx / 2)]

theorem walkCorduroyMerklePathWith_build_eq (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (mkAdrs : Nat → Nat → CorduroyAdrs) (leafFn : Nat → Lane4) :
    ∀ (rem lvl idx : Nat),
      walkCorduroyMerklePathWith eng pkSeed mkAdrs lvl idx
        (computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn lvl idx)
        (buildCorduroyMerklePathWith eng pkSeed mkAdrs leafFn rem lvl idx) =
      computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn (lvl + rem) (idx / (2 ^ rem))
  | 0, lvl, idx => by simp [buildCorduroyMerklePathWith, walkCorduroyMerklePathWith]
  | rem + 1, lvl, idx => by
    dsimp only [buildCorduroyMerklePathWith, walkCorduroyMerklePathWith]
    have hParentEq :
        (if idx % 2 == 0 then
          corduroyMerkleHashWith eng pkSeed (mkAdrs lvl (idx / 2))
            (computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn lvl idx)
            (computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn lvl (if idx % 2 == 0 then idx + 1 else idx - 1))
         else
          corduroyMerkleHashWith eng pkSeed (mkAdrs lvl (idx / 2))
            (computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn lvl (if idx % 2 == 0 then idx + 1 else idx - 1))
            (computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn lvl idx)) =
        computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn (lvl + 1) (idx / 2) := by
      rcases Nat.mod_two_eq_zero_or_one idx with hEven | hOdd
      · have hIdx : 2 * (idx / 2) = idx := by omega
        simp only [hEven, beq_self_eq_true, ↓reduceIte, computeCorduroyMerkleNodeWith, hIdx]
      · have hNe : (idx % 2 == 0) = false := by rw [hOdd]; decide
        have hSib : 2 * (idx / 2) = idx - 1 := by omega
        have hSubAdd : idx - 1 + 1 = idx := by omega
        simp only [hNe, Bool.false_eq_true, ↓reduceIte, computeCorduroyMerkleNodeWith, hSib, hSubAdd]
    rw [hParentEq, walkCorduroyMerklePathWith_build_eq eng pkSeed mkAdrs leafFn rem (lvl + 1) (idx / 2)]
    have hLvl : (lvl + 1) + rem = lvl + (rem + 1) := by omega
    have hDiv : (idx / 2) / (2 ^ rem) = idx / (2 ^ (rem + 1)) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ rem)]
    rw [hLvl, hDiv]

/-! ### `Corduroy` Key Derivation, FORS, WOTS+C Layers, Standalone Signer & Verifier -/

/-- Honest WOTS+C chain peaks (`step = 3`) for keypair `(layer, treeIdx, kpIdx)`. -/
def corduroyHonestWotsPeaksWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (layer treeIdx kpIdx : Nat) : List Lane4 :=
  (List.range cfg.wotsChains).map fun c =>
    corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx c 0 3
      (corduroyWotsSecretWith eng sk layer treeIdx kpIdx c)

def corduroyHonestWotsPeaks (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (layer treeIdx kpIdx : Nat) : List Lane4 :=
  corduroyHonestWotsPeaksWith corduroyPoseidon2Engine cfg sk layer treeIdx kpIdx

/-- Honest WOTS+C public key (`T_ℓ`) at `(layer, treeIdx, kpIdx)`. -/
def corduroyHonestWotsPkWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (layer treeIdx kpIdx : Nat) : Lane4 :=
  corduroyWotsPkCompressWith eng sk.pkSeed layer treeIdx kpIdx
    (corduroyHonestWotsPeaksWith eng cfg sk layer treeIdx kpIdx)

def corduroyHonestWotsPk (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (layer treeIdx kpIdx : Nat) : Lane4 :=
  corduroyHonestWotsPkWith corduroyPoseidon2Engine cfg sk layer treeIdx kpIdx

/-- Honest XMSS subtree root of height `cfg.subtreeHeight` at `(layer, treeIdx)`. -/
def corduroyHonestSubtreeRootWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (layer treeIdx : Nat) : Lane4 :=
  computeCorduroyMerkleNodeWith eng sk.pkSeed (xmssMerkleAdrs layer treeIdx)
    (corduroyHonestWotsPkWith eng cfg sk layer treeIdx) cfg.subtreeHeight 0

def corduroyHonestSubtreeRoot (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (layer treeIdx : Nat) : Lane4 :=
  corduroyHonestSubtreeRootWith corduroyPoseidon2Engine cfg sk layer treeIdx

/-- Derive the `Corduroy` public key from the top hypertree layer `d - 1`, `treeIdx = 0`. -/
def corduroyDerivePkWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey) : CorduroyPublicKey :=
  { pkSeed := sk.pkSeed
    pkRoot := corduroyHonestSubtreeRootWith eng cfg sk (cfg.numLayers - 1) 0 }

@[expose] def corduroyDerivePk (cfg : CorduroyParams) (sk : CorduroySecretKey) : CorduroyPublicKey :=
  corduroyDerivePkWith corduroyPoseidon2Engine cfg sk

/-- Honest FORS public leaf at `(leafGlobalIdx, treeJ, leafIdx)`. -/
def corduroyHonestForsLeafWith (eng : CorduroyPermEngine) (sk : CorduroySecretKey)
    (leafGlobalIdx treeJ leafIdx : Nat) : Lane4 :=
  corduroyForsLeafHashWith eng sk.pkSeed leafGlobalIdx treeJ leafIdx
    (corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx)

def corduroyHonestForsLeaf (sk : CorduroySecretKey) (leafGlobalIdx treeJ leafIdx : Nat) : Lane4 :=
  corduroyHonestForsLeafWith corduroyPoseidon2Engine sk leafGlobalIdx treeJ leafIdx

/-- Honest FORS tree root `j < cfg.forsTrees` at `leafGlobalIdx`. -/
def corduroyHonestForsTreeRootWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (leafGlobalIdx treeJ : Nat) : Lane4 :=
  computeCorduroyMerkleNodeWith eng sk.pkSeed (forsNodeAdrs leafGlobalIdx treeJ)
    (corduroyHonestForsLeafWith eng sk leafGlobalIdx treeJ) cfg.forsHeight 0

def corduroyHonestForsTreeRoot (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (leafGlobalIdx treeJ : Nat) : Lane4 :=
  corduroyHonestForsTreeRootWith corduroyPoseidon2Engine cfg sk leafGlobalIdx treeJ

/-- Honest FORS public key (`T_k`) at `leafGlobalIdx`. -/
def corduroyHonestForsPkWith (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (sk : CorduroySecretKey) (leafGlobalIdx : Nat) : Lane4 :=
  let roots := (List.range cfg.forsTrees).map (corduroyHonestForsTreeRootWith eng cfg sk leafGlobalIdx)
  corduroyForsRootsCompressWith eng sk.pkSeed leafGlobalIdx roots

def corduroyHonestForsPk (cfg : CorduroyParams) (sk : CorduroySecretKey) (leafGlobalIdx : Nat) : Lane4 :=
  corduroyHonestForsPkWith corduroyPoseidon2Engine cfg sk leafGlobalIdx

/-- Single FORS tree opening `(secretVal, authPath)`. -/
structure CorduroyForsOpening where
  secretVal : Lane4
  authPath  : List Lane4
  deriving DecidableEq, Repr

/-- Single hypertree layer WOTS+C + Merkle signature `(tswCtr, wotsChains, authPath)`. -/
structure CorduroyLayerSig where
  tswCtr     : Nat
  wotsChains : List Lane4
  authPath   : List Lane4
  deriving DecidableEq, Repr

/-- Complete stateless `Corduroy` hypertree signature `(rRand, forsOpenings, layerSigs)`. -/
structure CorduroySig where
  rRand        : Lane4
  forsOpenings : List CorduroyForsOpening
  layerSigs    : List CorduroyLayerSig
  deriving DecidableEq, Repr

/-- Complete WOTS+C chain peaks from signature chain nodes `chains` and digits `digits`. -/
def corduroyRecoverPeaksWith (eng : CorduroyPermEngine) (pkSeed : Lane4) (layer treeIdx kpIdx c : Nat)
    (digits : List Nat) (chains : List Lane4) : List Lane4 :=
  match digits, chains with
  | [], _ => []
  | _, [] => []
  | d :: ds, ch :: chs =>
    corduroyChainIterWith eng pkSeed layer treeIdx kpIdx c d (3 - d) ch ::
      corduroyRecoverPeaksWith eng pkSeed layer treeIdx kpIdx (c + 1) ds chs
  termination_by structural digits

def corduroyRecoverPeaks (pkSeed : Lane4) (layer treeIdx kpIdx c : Nat)
    (digits : List Nat) (chains : List Lane4) : List Lane4 :=
  corduroyRecoverPeaksWith corduroyPoseidon2Engine pkSeed layer treeIdx kpIdx c digits chains

theorem corduroyRecoverPeaksWith_honest (eng : CorduroyPermEngine) (pkSeed : Lane4) (sk : CorduroySecretKey)
    (hSeed : pkSeed = sk.pkSeed) (layer treeIdx kpIdx : Nat) :
    ∀ (digits : List Nat) (startC : Nat),
      (∀ d ∈ digits, d < 4) →
      corduroyRecoverPeaksWith eng pkSeed layer treeIdx kpIdx startC digits
        ((List.range digits.length).map fun i =>
          corduroyChainIterWith eng pkSeed layer treeIdx kpIdx (startC + i) 0 (digits[i]!)
            (corduroyWotsSecretWith eng sk layer treeIdx kpIdx (startC + i))) =
      (List.range digits.length).map fun i =>
        corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx (startC + i) 0 3
          (corduroyWotsSecretWith eng sk layer treeIdx kpIdx (startC + i))
  | [], _, _ => rfl
  | d :: ds, startC, hLt => by
    subst hSeed
    have hdLt : d < 4 := hLt d (List.mem_cons_self ..)
    have hTailLt : ∀ x ∈ ds, x < 4 := fun x hx => hLt x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero]
    dsimp only [corduroyRecoverPeaksWith]
    have hd0 : (d :: ds)[0]! = d := rfl
    have hAdd0 := corduroyChainIterWith_add eng sk.pkSeed layer treeIdx kpIdx startC d (3 - d) 0
      (corduroyWotsSecretWith eng sk layer treeIdx kpIdx startC)
    rw [Nat.zero_add] at hAdd0
    rw [hd0, hAdd0]
    have hd3 : d + (3 - d) = 3 := by omega
    rw [hd3]
    congr 1
    rw [List.map_map, List.map_map]
    have hShiftMap :
        (List.map ((fun i => corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx (startC + i) 0
            ((d :: ds)[i]!) (corduroyWotsSecretWith eng sk layer treeIdx kpIdx (startC + i))) ∘ Nat.succ)
          (List.range ds.length)) =
        (List.map (fun i => corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx ((startC + 1) + i) 0
            (ds[i]!) (corduroyWotsSecretWith eng sk layer treeIdx kpIdx ((startC + 1) + i)))
          (List.range ds.length)) := by
      apply List.map_congr_left
      intro i _
      dsimp only [Function.comp]
      have hAssoc : startC + (i + 1) = (startC + 1) + i := by omega
      have hGet : (d :: ds)[i + 1]! = ds[i]! := rfl
      rw [hAssoc, hGet]
    rw [hShiftMap, corduroyRecoverPeaksWith_honest eng sk.pkSeed sk rfl layer treeIdx kpIdx ds (startC + 1) hTailLt]
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp]
    have hAssoc : (startC + 1) + i = startC + (i + 1) := by omega
    rw [hAssoc]

/-- Verify FORS openings at `leafGlobalIdx` against `forsIndices` and recover `forsPk`. -/
def corduroyVerifyForsTreesWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (pkSeed : Lane4)
    (leafGlobalIdx j : Nat) (forsIndices : List Nat) (openings : List CorduroyForsOpening) : Option (List Lane4) :=
  match forsIndices, openings with
  | [], [] => some []
  | idx :: idxs, op :: ops =>
    if !(decide (idx < 2 ^ cfg.forsHeight) && (op.authPath.length == cfg.forsHeight)) then none
    else
      let leaf := corduroyForsLeafHashWith eng pkSeed leafGlobalIdx j idx op.secretVal
      let rt := walkCorduroyMerklePathWith eng pkSeed (forsNodeAdrs leafGlobalIdx j) 0 idx leaf op.authPath
      match corduroyVerifyForsTreesWith eng cfg pkSeed leafGlobalIdx (j + 1) idxs ops with
      | none => none
      | some restRts => some (rt :: restRts)
  | _, _ => none
  termination_by structural forsIndices

def corduroyVerifyForsTrees (cfg : CorduroyParams) (pkSeed : Lane4) (leafGlobalIdx j : Nat)
    (forsIndices : List Nat) (openings : List CorduroyForsOpening) : Option (List Lane4) :=
  corduroyVerifyForsTreesWith corduroyPoseidon2Engine cfg pkSeed leafGlobalIdx j forsIndices openings

def corduroyRecoverForsPkWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (pkSeed : Lane4)
    (leafGlobalIdx : Nat) (forsIndices : List Nat) (ops : List CorduroyForsOpening) : Option Lane4 :=
  if !(forsIndices.length == cfg.forsTrees && ops.length == cfg.forsTrees) then none
  else
    match corduroyVerifyForsTreesWith eng cfg pkSeed leafGlobalIdx 0 forsIndices ops with
    | none => none
    | some roots => some (corduroyForsRootsCompressWith eng pkSeed leafGlobalIdx roots)

def corduroyRecoverForsPk (cfg : CorduroyParams) (pkSeed : Lane4) (leafGlobalIdx : Nat)
    (forsIndices : List Nat) (ops : List CorduroyForsOpening) : Option Lane4 :=
  corduroyRecoverForsPkWith corduroyPoseidon2Engine cfg pkSeed leafGlobalIdx forsIndices ops

/-- Verify a single hypertree layer `(layer, treeIdx, kpIdx)` signing `childRoot`. -/
def corduroyVerifyLayerWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (pk : CorduroyPublicKey)
    (layer treeIdx kpIdx : Nat) (childRoot : Lane4) (lsig : CorduroyLayerSig) : Option Lane4 :=
  if !(lsig.wotsChains.length == cfg.wotsChains && lsig.authPath.length == cfg.subtreeHeight &&
       decide (lsig.tswCtr < 2 ^ 56)) then none
  else
    let hmsg := corduroyLayerHmsgWith eng pk layer treeIdx kpIdx lsig.tswCtr childRoot
    let digits := corduroyExtractDigits cfg.wotsChains hmsg
    if !(natListSum digits == cfg.targetSum) then none
    else
      let peaks := corduroyRecoverPeaksWith eng pk.pkSeed layer treeIdx kpIdx 0 digits lsig.wotsChains
      let wotsPk := corduroyWotsPkCompressWith eng pk.pkSeed layer treeIdx kpIdx peaks
      some (walkCorduroyMerklePathWith eng pk.pkSeed (xmssMerkleAdrs layer treeIdx) 0 kpIdx wotsPk lsig.authPath)

def corduroyVerifyLayer (cfg : CorduroyParams) (pk : CorduroyPublicKey)
    (layer treeIdx kpIdx : Nat) (childRoot : Lane4) (lsig : CorduroyLayerSig) : Option Lane4 :=
  corduroyVerifyLayerWith corduroyPoseidon2Engine cfg pk layer treeIdx kpIdx childRoot lsig

/-- Verify `d` hypertree layers climbing from `(layer, remIdx, curRoot)` to the top root. -/
def corduroyVerifyHypertreeWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (pk : CorduroyPublicKey)
    (layer remIdx : Nat) (curRoot : Lane4) (lsigs : List CorduroyLayerSig) : Option Lane4 :=
  match lsigs with
  | [] => some curRoot
  | lsig :: rest =>
    let subLeaves := 2 ^ cfg.subtreeHeight
    let kpIdx := remIdx % subLeaves
    let treeIdx := remIdx / subLeaves
    match corduroyVerifyLayerWith eng cfg pk layer treeIdx kpIdx curRoot lsig with
    | none => none
    | some nextRoot => corduroyVerifyHypertreeWith eng cfg pk (layer + 1) treeIdx nextRoot rest
  termination_by structural lsigs

def corduroyVerifyHypertree (cfg : CorduroyParams) (pk : CorduroyPublicKey)
    (layer remIdx : Nat) (curRoot : Lane4) (lsigs : List CorduroyLayerSig) : Option Lane4 :=
  corduroyVerifyHypertreeWith corduroyPoseidon2Engine cfg pk layer remIdx curRoot lsigs

def corduroyVerifyWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (pk : CorduroyPublicKey)
    (msg : Lane4) (sig : CorduroySig) : Bool :=
  if !(cfg.wellFormed && (sig.layerSigs.length == cfg.numLayers)) then false
  else
    let (leafGlobalIdx, forsIndices, _) := corduroyHashMsgWith eng cfg sig.rRand pk msg
    match corduroyRecoverForsPkWith eng cfg pk.pkSeed leafGlobalIdx forsIndices sig.forsOpenings with
    | none => false
    | some forsPk =>
      match corduroyVerifyHypertreeWith eng cfg pk 0 leafGlobalIdx forsPk sig.layerSigs with
      | none => false
      | some topRoot => topRoot == pk.pkRoot

/-- **Standalone `Corduroy` Verifier (`corduroyVerify`)** matching `Corduroy::verify` in `corduroy.rs`. -/
@[expose] def corduroyVerify (cfg : CorduroyParams) (pk : CorduroyPublicKey)
    (msg : Lane4) (sig : CorduroySig) : Bool :=
  corduroyVerifyWith corduroyPoseidon2Engine cfg pk msg sig

/-- Randomness + counter-grinding schedule `(optRand, layerCtrs)` for deterministic `Corduroy` signing. -/
structure CorduroySignRand where
  optRand   : Lane4
  layerCtrs : List Nat
  deriving DecidableEq, Repr

/-- Validity predicate for a `CorduroySignRand`: every layer counter `ctrs[L] < 2^56` hits `targetSum`. -/
def CorduroyValidGrindWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (msg : Lane4) (r : CorduroySignRand) : Prop :=
  cfg.wellFormed = true ∧
  r.layerCtrs.length = cfg.numLayers ∧
  let pk := corduroyDerivePkWith eng cfg sk
  let rRand := corduroyPrfMsgWith eng sk r.optRand msg
  let leafGlobalIdx := (corduroyHashMsgWith eng cfg rRand pk msg).1
  ∀ (L : Nat) (hL : L < r.layerCtrs.length),
    let ctr := r.layerCtrs[L]'hL
    let remL := leafGlobalIdx / (2 ^ (L * cfg.subtreeHeight))
    let kpL := remL % (2 ^ cfg.subtreeHeight)
    let trL := remL / (2 ^ cfg.subtreeHeight)
    let childRt :=
      if L = 0 then corduroyHonestForsPkWith eng cfg sk leafGlobalIdx
      else corduroyHonestSubtreeRootWith eng cfg sk (L - 1) remL
    ctr < 2 ^ 56 ∧
    natListSum (corduroyExtractDigits cfg.wotsChains (corduroyLayerHmsgWith eng pk L trL kpL ctr childRt)) = cfg.targetSum

def CorduroyValidGrind (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (msg : Lane4) (r : CorduroySignRand) : Prop :=
  CorduroyValidGrindWith corduroyPoseidon2Engine cfg sk msg r

def corduroyBuildForsOpeningsWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (leafGlobalIdx j : Nat) (forsIndices : List Nat) : List CorduroyForsOpening :=
  match forsIndices with
  | [] => []
  | idx :: idxs =>
    let sec := corduroyForsSecretWith eng sk leafGlobalIdx j idx
    let path := buildCorduroyMerklePathWith eng sk.pkSeed (forsNodeAdrs leafGlobalIdx j)
      (corduroyHonestForsLeafWith eng sk leafGlobalIdx j) cfg.forsHeight 0 idx
    { secretVal := sec, authPath := path } ::
      corduroyBuildForsOpeningsWith eng cfg sk leafGlobalIdx (j + 1) idxs
  termination_by structural forsIndices

def corduroyBuildForsOpenings (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (leafGlobalIdx j : Nat) (forsIndices : List Nat) : List CorduroyForsOpening :=
  corduroyBuildForsOpeningsWith corduroyPoseidon2Engine cfg sk leafGlobalIdx j forsIndices

def corduroySignLayersAuxWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (pk : CorduroyPublicKey) (layer remIdx : Nat) (curRoot : Lane4) (ctrs : List Nat) : List CorduroyLayerSig :=
  match ctrs with
  | [] => []
  | ctr :: restCtrs =>
    let subLeaves := 2 ^ cfg.subtreeHeight
    let kpIdx := remIdx % subLeaves
    let treeIdx := remIdx / subLeaves
    let hmsg := corduroyLayerHmsgWith eng pk layer treeIdx kpIdx ctr curRoot
    let digits := corduroyExtractDigits cfg.wotsChains hmsg
    let chains := (List.range cfg.wotsChains).map fun c =>
      corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx c 0 (digits[c]!)
        (corduroyWotsSecretWith eng sk layer treeIdx kpIdx c)
    let path := buildCorduroyMerklePathWith eng sk.pkSeed (xmssMerkleAdrs layer treeIdx)
      (corduroyHonestWotsPkWith eng cfg sk layer treeIdx) cfg.subtreeHeight 0 kpIdx
    let nextRoot := corduroyHonestSubtreeRootWith eng cfg sk layer treeIdx
    { tswCtr := ctr, wotsChains := chains, authPath := path } ::
      corduroySignLayersAuxWith eng cfg sk pk (layer + 1) treeIdx nextRoot restCtrs
  termination_by structural ctrs

def corduroySignLayersAux (cfg : CorduroyParams) (sk : CorduroySecretKey) (pk : CorduroyPublicKey)
    (layer remIdx : Nat) (curRoot : Lane4) (ctrs : List Nat) : List CorduroyLayerSig :=
  corduroySignLayersAuxWith corduroyPoseidon2Engine cfg sk pk layer remIdx curRoot ctrs

def corduroySignWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (msg : Lane4) (r : CorduroySignRand) : CorduroySig :=
  let pk := corduroyDerivePkWith eng cfg sk
  let rRand := corduroyPrfMsgWith eng sk r.optRand msg
  let (leafGlobalIdx, forsIndices, _) := corduroyHashMsgWith eng cfg rRand pk msg
  let forsOps := corduroyBuildForsOpeningsWith eng cfg sk leafGlobalIdx 0 forsIndices
  let forsPk := corduroyHonestForsPkWith eng cfg sk leafGlobalIdx
  let layerSigs := corduroySignLayersAuxWith eng cfg sk pk 0 leafGlobalIdx forsPk r.layerCtrs
  { rRand := rRand, forsOpenings := forsOps, layerSigs := layerSigs }

/-- **Standalone `Corduroy` Signer (`corduroySign`)**. -/
@[expose] def corduroySign (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (msg : Lane4) (r : CorduroySignRand) : CorduroySig :=
  corduroySignWith corduroyPoseidon2Engine cfg sk msg r

/-- Bounded counter search (`ctr = startCtr .. startCtr + fuel - 1`) for WOTS+C `targetSum` grinding. -/
def corduroyGrindLayerCounterWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (pk : CorduroyPublicKey)
    (layer treeIdx kpIdx : Nat) (childRoot : Lane4) (ctr fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | f + 1 =>
    if decide (ctr < 2 ^ 56) &&
       (natListSum (corduroyExtractDigits cfg.wotsChains
          (corduroyLayerHmsgWith eng pk layer treeIdx kpIdx ctr childRoot)) == cfg.targetSum) then
      some ctr
    else
      corduroyGrindLayerCounterWith eng cfg pk layer treeIdx kpIdx childRoot (ctr + 1) f
  termination_by structural fuel

def corduroyGrindLayerCounter (cfg : CorduroyParams) (pk : CorduroyPublicKey)
    (layer treeIdx kpIdx : Nat) (childRoot : Lane4) (ctr fuel : Nat) : Option Nat :=
  corduroyGrindLayerCounterWith corduroyPoseidon2Engine cfg pk layer treeIdx kpIdx childRoot ctr fuel

private theorem corduroyVerifyForsTreesWith_honest (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (sk : CorduroySecretKey) (leafGlobalIdx : Nat) :
    ∀ (idxs : List Nat) (startJ : Nat),
      (∀ idx ∈ idxs, idx < 2 ^ cfg.forsHeight) →
      (corduroyBuildForsOpeningsWith eng cfg sk leafGlobalIdx startJ idxs).length = idxs.length ∧
      corduroyVerifyForsTreesWith eng cfg sk.pkSeed leafGlobalIdx startJ idxs
        (corduroyBuildForsOpeningsWith eng cfg sk leafGlobalIdx startJ idxs) =
      some ((List.range idxs.length).map fun t =>
        corduroyHonestForsTreeRootWith eng cfg sk leafGlobalIdx (startJ + t))
  | [], _, _ => ⟨rfl, rfl⟩
  | idx :: idxs, startJ, hB => by
    have hIdxLt : idx < 2 ^ cfg.forsHeight := hB idx (List.mem_cons_self ..)
    have hTailB : ∀ x ∈ idxs, x < 2 ^ cfg.forsHeight := fun x hx => hB x (List.mem_cons_of_mem _ hx)
    obtain ⟨ihLen, ihVer⟩ := corduroyVerifyForsTreesWith_honest eng cfg sk leafGlobalIdx idxs (startJ + 1) hTailB
    refine ⟨by simp [corduroyBuildForsOpeningsWith, ihLen], ?_⟩
    dsimp only [corduroyBuildForsOpeningsWith, corduroyVerifyForsTreesWith]
    have hPathLen : (buildCorduroyMerklePathWith eng sk.pkSeed (forsNodeAdrs leafGlobalIdx startJ)
        (corduroyHonestForsLeafWith eng sk leafGlobalIdx startJ) cfg.forsHeight 0 idx).length = cfg.forsHeight :=
      buildCorduroyMerklePathWith_length _ _ _ _ _ _ _
    simp only [hIdxLt, decide_true, hPathLen, beq_self_eq_true, Bool.and_self, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, ihVer]
    have hWalk := walkCorduroyMerklePathWith_build_eq eng sk.pkSeed (forsNodeAdrs leafGlobalIdx startJ)
      (corduroyHonestForsLeafWith eng sk leafGlobalIdx startJ) cfg.forsHeight 0 idx
    have hLeafEq : corduroyForsLeafHashWith eng sk.pkSeed leafGlobalIdx startJ idx
        (corduroyForsSecretWith eng sk leafGlobalIdx startJ idx) =
        computeCorduroyMerkleNodeWith eng sk.pkSeed (forsNodeAdrs leafGlobalIdx startJ)
          (corduroyHonestForsLeafWith eng sk leafGlobalIdx startJ) 0 idx := rfl
    rw [hLeafEq, hWalk, Nat.zero_add, Nat.div_eq_of_lt hIdxLt]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero, Option.some.injEq, List.cons.injEq]
    refine ⟨rfl, ?_⟩
    rw [List.map_map]
    apply List.map_congr_left
    intro t _
    dsimp only [Function.comp]
    have hAssoc : (startJ + 1) + t = startJ + (t + 1) := by omega
    rw [hAssoc]

private theorem corduroySignLayersAuxWith_spec (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (sk : CorduroySecretKey) (pk : CorduroyPublicKey) (hSeed : pk.pkSeed = sk.pkSeed)
    (hChainsLe : cfg.wotsChains ≤ 128) :
    ∀ (ctrs : List Nat) (startL remIdx : Nat) (curRoot : Lane4),
      (∀ (j : Nat) (hj : j < ctrs.length),
        let L := startL + j
        let curRem := remIdx / (2 ^ (j * cfg.subtreeHeight))
        let kpL := curRem % (2 ^ cfg.subtreeHeight)
        let trL := curRem / (2 ^ cfg.subtreeHeight)
        let childRt := if j = 0 then curRoot else corduroyHonestSubtreeRootWith eng cfg sk (L - 1) curRem
        (ctrs[j]'hj) < 2 ^ 56 ∧
        natListSum (corduroyExtractDigits cfg.wotsChains
          (corduroyLayerHmsgWith eng pk L trL kpL (ctrs[j]'hj) childRt)) = cfg.targetSum) →
      (corduroySignLayersAuxWith eng cfg sk pk startL remIdx curRoot ctrs).length = ctrs.length ∧
      (0 < ctrs.length →
        corduroyVerifyHypertreeWith eng cfg pk startL remIdx curRoot
          (corduroySignLayersAuxWith eng cfg sk pk startL remIdx curRoot ctrs) =
        some (corduroyHonestSubtreeRootWith eng cfg sk (startL + ctrs.length - 1)
                (remIdx / (2 ^ (ctrs.length * cfg.subtreeHeight)))))
  | [], _, _, _, _ => ⟨rfl, fun h => absurd h (Nat.not_lt_zero 0)⟩
  | ctr :: rest, startL, remIdx, curRoot, hValid => by
    have h0 := hValid 0 (Nat.zero_lt_succ _)
    simp only [Nat.add_zero, Nat.zero_mul, Nat.pow_zero, Nat.div_one, ↓reduceIte, List.getElem_cons_zero] at h0
    rcases h0 with ⟨hCtrLt, hSum0⟩
    let subLeaves := 2 ^ cfg.subtreeHeight
    let kp0 := remIdx % subLeaves
    let tr0 := remIdx / subLeaves
    have hKp0Lt : kp0 < subLeaves := Nat.mod_lt _ (Nat.two_pow_pos _)
    let hmsg0 := corduroyLayerHmsgWith eng pk startL tr0 kp0 ctr curRoot
    let digits0 := corduroyExtractDigits cfg.wotsChains hmsg0
    obtain ⟨hDigLen, hDigLt⟩ := corduroyExtractDigits_spec hChainsLe hmsg0
    have hVer0 : corduroyVerifyLayerWith eng cfg pk startL tr0 kp0 curRoot
        { tswCtr := ctr
          wotsChains := (List.range cfg.wotsChains).map fun c =>
            corduroyChainIterWith eng sk.pkSeed startL tr0 kp0 c 0 (digits0[c]!)
              (corduroyWotsSecretWith eng sk startL tr0 kp0 c)
          authPath := buildCorduroyMerklePathWith eng sk.pkSeed (xmssMerkleAdrs startL tr0)
            (corduroyHonestWotsPkWith eng cfg sk startL tr0) cfg.subtreeHeight 0 kp0 } =
        some (corduroyHonestSubtreeRootWith eng cfg sk startL tr0) := by
      unfold corduroyVerifyLayerWith
      have hPathLen := buildCorduroyMerklePathWith_length eng sk.pkSeed (xmssMerkleAdrs startL tr0)
        (corduroyHonestWotsPkWith eng cfg sk startL tr0) cfg.subtreeHeight 0 kp0
      simp only [List.length_map, List.length_range, hPathLen, hCtrLt, decide_true,
        beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hDigSum0 : natListSum digits0 = cfg.targetSum := hSum0
      change (if !(natListSum digits0 == cfg.targetSum) then none else _) = _
      rw [hDigSum0]
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      have hZeroShift :
          ((List.range cfg.wotsChains).map fun c =>
            corduroyChainIterWith eng sk.pkSeed startL tr0 kp0 c 0 (digits0[c]!)
              (corduroyWotsSecretWith eng sk startL tr0 kp0 c)) =
          ((List.range digits0.length).map fun i =>
            corduroyChainIterWith eng pk.pkSeed startL tr0 kp0 (0 + i) 0 (digits0[i]!)
              (corduroyWotsSecretWith eng sk startL tr0 kp0 (0 + i))) := by
        rw [hDigLen, hSeed]
        apply List.map_congr_left
        intro i _; rw [Nat.zero_add]
      rw [hZeroShift, corduroyRecoverPeaksWith_honest eng pk.pkSeed sk hSeed startL tr0 kp0 digits0 0 hDigLt]
      have hPeaksEq :
          ((List.range digits0.length).map fun i =>
            corduroyChainIterWith eng sk.pkSeed startL tr0 kp0 (0 + i) 0 3
              (corduroyWotsSecretWith eng sk startL tr0 kp0 (0 + i))) =
          corduroyHonestWotsPeaksWith eng cfg sk startL tr0 kp0 := by
        unfold corduroyHonestWotsPeaksWith
        rw [hDigLen]
        apply List.map_congr_left; intro i _; rw [Nat.zero_add]
      rw [hPeaksEq, hSeed]
      have hWotsEq : corduroyWotsPkCompressWith eng sk.pkSeed startL tr0 kp0
          (corduroyHonestWotsPeaksWith eng cfg sk startL tr0 kp0) =
          computeCorduroyMerkleNodeWith eng sk.pkSeed (xmssMerkleAdrs startL tr0)
            (corduroyHonestWotsPkWith eng cfg sk startL tr0) 0 kp0 := rfl
      rw [hWotsEq, walkCorduroyMerklePathWith_build_eq eng sk.pkSeed (xmssMerkleAdrs startL tr0)
            (corduroyHonestWotsPkWith eng cfg sk startL tr0) cfg.subtreeHeight 0 kp0,
          Nat.zero_add, Nat.div_eq_of_lt hKp0Lt]
      rfl
    have hRestValid :
        ∀ (j : Nat) (hj : j < rest.length),
          let L := (startL + 1) + j
          let curRem := tr0 / (2 ^ (j * cfg.subtreeHeight))
          let kpL := curRem % (2 ^ cfg.subtreeHeight)
          let trL := curRem / (2 ^ cfg.subtreeHeight)
          let childRt := if j = 0 then corduroyHonestSubtreeRootWith eng cfg sk startL tr0
                         else corduroyHonestSubtreeRootWith eng cfg sk (L - 1) curRem
          (rest[j]'hj) < 2 ^ 56 ∧
          natListSum (corduroyExtractDigits cfg.wotsChains
            (corduroyLayerHmsgWith eng pk L trL kpL (rest[j]'hj) childRt)) = cfg.targetSum := by
      intro j hj
      have hStep := hValid (j + 1) (Nat.succ_lt_succ hj)
      dsimp only at hStep ⊢
      have hL : startL + (j + 1) = (startL + 1) + j := by omega
      have hDiv : tr0 / (2 ^ (j * cfg.subtreeHeight)) = remIdx / (2 ^ ((j + 1) * cfg.subtreeHeight)) := by
        dsimp only [tr0, subLeaves]
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have hE : cfg.subtreeHeight + j * cfg.subtreeHeight = (j + 1) * cfg.subtreeHeight := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rw [hE]
      have hChild :
          (if j = 0 then corduroyHonestSubtreeRootWith eng cfg sk startL tr0
           else corduroyHonestSubtreeRootWith eng cfg sk ((startL + 1) + j - 1)
             (remIdx / 2 ^ ((j + 1) * cfg.subtreeHeight))) =
          (if j + 1 = 0 then curRoot
           else corduroyHonestSubtreeRootWith eng cfg sk (startL + (j + 1) - 1)
             (remIdx / 2 ^ ((j + 1) * cfg.subtreeHeight))) := by
        dsimp only [tr0, subLeaves]
        by_cases hj0 : j = 0
        · subst hj0
          simp only [↓reduceIte, Nat.zero_add, Nat.one_mul, Nat.add_sub_cancel, show ¬(1 = 0) by decide]
        · simp only [hj0, Nat.succ_ne_zero, ↓reduceIte, hL]
      rw [List.getElem_cons_succ] at hStep
      rw [hDiv, hChild, ← hL]
      exact hStep
    obtain ⟨ihLen, ihVer⟩ := corduroySignLayersAuxWith_spec eng cfg sk pk hSeed hChainsLe
      rest (startL + 1) tr0 (corduroyHonestSubtreeRootWith eng cfg sk startL tr0) hRestValid
    refine ⟨by dsimp only [corduroySignLayersAuxWith]; exact congrArg Nat.succ ihLen, fun _ => ?_⟩
    dsimp only [corduroySignLayersAuxWith, corduroyVerifyHypertreeWith]
    change (match corduroyVerifyLayerWith eng cfg pk startL tr0 kp0 curRoot _ with
            | none => none
            | some nextRoot => corduroyVerifyHypertreeWith eng cfg pk (startL + 1) tr0 nextRoot
                (corduroySignLayersAuxWith eng cfg sk pk (startL + 1) tr0
                  (corduroyHonestSubtreeRootWith eng cfg sk startL tr0) rest)) = _
    rw [hVer0]
    dsimp only
    cases rest with
    | nil =>
      dsimp only [corduroySignLayersAuxWith, corduroyVerifyHypertreeWith]
      simp only [List.length_singleton, Nat.add_sub_cancel, Nat.one_mul]
      rfl
    | cons ctr1 tail =>
      rw [ihVer (Nat.zero_lt_succ _)]
      have hEndL : (startL + 1) + (ctr1 :: tail).length - 1 = startL + (ctr :: ctr1 :: tail).length - 1 := by
        simp only [List.length_cons]; omega
      have hEndDiv : tr0 / (2 ^ ((ctr1 :: tail).length * cfg.subtreeHeight)) =
          remIdx / (2 ^ ((ctr :: ctr1 :: tail).length * cfg.subtreeHeight)) := by
        dsimp only [tr0, subLeaves]
        simp only [List.length_cons]
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have hE : cfg.subtreeHeight + (tail.length + 1) * cfg.subtreeHeight =
            (tail.length + 1 + 1) * cfg.subtreeHeight := by
          rw [Nat.add_mul (tail.length + 1) 1 cfg.subtreeHeight, Nat.one_mul, Nat.add_comm]
        rw [hE]
      rw [hEndL, hEndDiv]

/-- **Standalone `Corduroy` Signing Completeness (`corduroyVerify_corduroySign`)**:
    Every signature produced by `corduroySign cfg sk msg r` under a valid TSW counter schedule
    passes `corduroyVerify cfg (corduroyDerivePk cfg sk) msg (corduroySign cfg sk msg r) = true`. -/
theorem corduroyVerifyWith_corduroySignWith
    (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey) (msg : Lane4) (r : CorduroySignRand)
    (hValid : CorduroyValidGrindWith eng cfg sk msg r) :
    corduroyVerifyWith eng cfg (corduroyDerivePkWith eng cfg sk) msg (corduroySignWith eng cfg sk msg r) = true := by
  rcases hValid with ⟨hWf, hCtrsLen, hLayers⟩
  have hUnpack : cfg.wotsChains ≤ 128 ∧ 0 < cfg.numLayers := by
    unfold CorduroyParams.wellFormed at hWf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
    exact ⟨hWf.1.1.1.1.1.1.1.1.1.1.2, hWf.1.1.1.1.1.1.1.2⟩
  rcases hUnpack with ⟨hChainsLe, hLayersPos⟩
  let pk := corduroyDerivePkWith eng cfg sk
  let rRand := corduroyPrfMsgWith eng sk r.optRand msg
  obtain ⟨hLeafLt, hForsIdxLen, hForsIdxBounds⟩ := corduroyHashMsgWith_bounds eng cfg rRand pk msg
  let leafGlobalIdx := (corduroyHashMsgWith eng cfg rRand pk msg).1
  let forsIndices := (corduroyHashMsgWith eng cfg rRand pk msg).2.1
  obtain ⟨hForsOpsLen, hForsVer⟩ := corduroyVerifyForsTreesWith_honest eng cfg sk leafGlobalIdx forsIndices 0 hForsIdxBounds
  have hRecFors : corduroyRecoverForsPkWith eng cfg pk.pkSeed leafGlobalIdx forsIndices
      (corduroyBuildForsOpeningsWith eng cfg sk leafGlobalIdx 0 forsIndices) =
      some (corduroyHonestForsPkWith eng cfg sk leafGlobalIdx) := by
    unfold corduroyRecoverForsPkWith
    have hSeed : pk.pkSeed = sk.pkSeed := rfl
    rw [hSeed, hForsOpsLen, hForsIdxLen]
    simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      hForsVer, Option.some.injEq]
    unfold corduroyHonestForsPkWith
    congr 1
    rw [hForsIdxLen]
    apply List.map_congr_left
    intro t _; rw [Nat.zero_add]
  have hAdapter :
      ∀ (j : Nat) (hj : j < r.layerCtrs.length),
        let L := 0 + j
        let curRem := leafGlobalIdx / (2 ^ (j * cfg.subtreeHeight))
        let kpL := curRem % (2 ^ cfg.subtreeHeight)
        let trL := curRem / (2 ^ cfg.subtreeHeight)
        let childRt := if j = 0 then corduroyHonestForsPkWith eng cfg sk leafGlobalIdx
                       else corduroyHonestSubtreeRootWith eng cfg sk (L - 1) curRem
        (r.layerCtrs[j]'hj) < 2 ^ 56 ∧
        natListSum (corduroyExtractDigits cfg.wotsChains
          (corduroyLayerHmsgWith eng pk L trL kpL (r.layerCtrs[j]'hj) childRt)) = cfg.targetSum := by
    intro j hj
    dsimp only [pk, rRand, leafGlobalIdx]
    simpa only [Nat.zero_add] using hLayers j hj
  obtain ⟨hSigLen, hHypVer⟩ := corduroySignLayersAuxWith_spec eng cfg sk pk rfl hChainsLe
    r.layerCtrs 0 leafGlobalIdx (corduroyHonestForsPkWith eng cfg sk leafGlobalIdx) hAdapter
  unfold corduroyVerifyWith corduroySignWith
  dsimp only [pk, rRand, leafGlobalIdx, forsIndices]
  rw [hSigLen, hCtrsLen, hWf]
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hRecFors]
  dsimp only
  rw [hHypVer (by omega)]
  dsimp only
  rw [beq_iff_eq, Nat.zero_add, hCtrsLen]
  have hTopTree : leafGlobalIdx / (2 ^ (cfg.numLayers * cfg.subtreeHeight)) = 0 :=
    Nat.div_eq_of_lt hLeafLt
  rw [hTopTree]
  rfl

theorem corduroyVerify_corduroySign
    (cfg : CorduroyParams) (sk : CorduroySecretKey) (msg : Lane4) (r : CorduroySignRand)
    (hValid : CorduroyValidGrind cfg sk msg r) :
    corduroyVerify cfg (corduroyDerivePk cfg sk) msg (corduroySign cfg sk msg r) = true :=
  corduroyVerifyWith_corduroySignWith corduroyPoseidon2Engine cfg sk msg r hValid

/-! ### Dealerless `(t, n)` Shamir/SPDZ Share-Level `Poseidon2` Threshold Engine (`corduroy_threshold_matches_standalone`) -/

/-- `(t, n)` Shamir secret-share bundle for `Corduroy`: each quorum party holds a 4-limb share of
    `skSeed` and a 4-limb share of `skPrf`, never reconstructing either secret in cleartext. -/
structure CorduroyKeyShares where
  skSeedShares : List Lane4
  skPrfShares  : List Lane4
  pkSeed       : Lane4
  deriving DecidableEq, Repr

/-- Validity of `CorduroyKeyShares` against Lagrange weights `lambdas` (`∑ λ_p = 1`). -/
def CorduroyKeyShares.MatchesSecret (lambdas : List Goldilocks)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) : Prop :=
  ringListSum lambdas = Goldilocks.one ∧
  sh.skSeedShares.length = lambdas.length ∧
  sh.skPrfShares.length = lambdas.length ∧
  lagrangeCombineLane4 lambdas sh.skSeedShares = sk.skSeed ∧
  lagrangeCombineLane4 lambdas sh.skPrfShares = sk.skPrf ∧
  sh.pkSeed = sk.pkSeed

private theorem lagrangeCombineLane4_replicate_public
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one) (v : Lane4) :
    lagrangeCombineLane4 lambdas (List.replicate lambdas.length v) = v := by
  have hRepMap : ∀ (f : Lane4 → Goldilocks),
      (List.replicate lambdas.length v).map f = List.replicate lambdas.length (f v) := by
    intro f; simp [List.map_replicate]
  rw [lagrangeCombineLane4_proj, hRepMap (·.x0), hRepMap (·.x1), hRepMap (·.x2), hRepMap (·.x3)]
  have hCol : ∀ c : Goldilocks, lagrangeCombine lambdas (List.replicate lambdas.length c) = c := fun c => by
    unfold lagrangeCombine
    rw [ringDot_replicate_right, hSumOne]
    exact LawfulCommRing.one_mul c
  rw [hCol, hCol, hCol, hCol]

private def zipAddLane4Shares : List Lane4 → List Lane4 → List Lane4
  | a :: as, b :: bs => lane4Add a b :: zipAddLane4Shares as bs
  | _, _ => []

private theorem goldMul_add_distrib (l a b : Goldilocks) :
    Goldilocks.mul l (Goldilocks.add a b) = Goldilocks.add (Goldilocks.mul l a) (Goldilocks.mul l b) :=
  LawfulCommRing.left_distrib l a b

private theorem goldAdd_four_rearrange (a b c d : Goldilocks) :
    Goldilocks.add (Goldilocks.add a b) (Goldilocks.add c d) =
    Goldilocks.add (Goldilocks.add a c) (Goldilocks.add b d) :=
  LawfulCommRing.add_add_add_comm a b c d

private theorem lane4Scale_add_distrib (l : Goldilocks) (a b : Lane4) :
    lane4Scale l (lane4Add a b) = lane4Add (lane4Scale l a) (lane4Scale l b) := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  unfold lane4Scale lane4Add
  dsimp only
  exact congrArg₄ Lane4.mk
    (goldMul_add_distrib l a0 b0)
    (goldMul_add_distrib l a1 b1)
    (goldMul_add_distrib l a2 b2)
    (goldMul_add_distrib l a3 b3)
where
  congrArg₄ {α β γ δ ε : Type} (f : α → β → γ → δ → ε)
      {a1 a2 : α} {b1 b2 : β} {c1 c2 : γ} {d1 d2 : δ}
      (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (hd : d1 = d2) :
      f a1 b1 c1 d1 = f a2 b2 c2 d2 := by
    subst ha hb hc hd; rfl

private theorem lane4Add_four_rearrange (a b c d : Lane4) :
    lane4Add (lane4Add a b) (lane4Add c d) = lane4Add (lane4Add a c) (lane4Add b d) := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  rcases c with ⟨c0, c1, c2, c3⟩
  rcases d with ⟨d0, d1, d2, d3⟩
  unfold lane4Add
  dsimp only
  have h0 := goldAdd_four_rearrange a0 b0 c0 d0
  have h1 := goldAdd_four_rearrange a1 b1 c1 d1
  have h2 := goldAdd_four_rearrange a2 b2 c2 d2
  have h3 := goldAdd_four_rearrange a3 b3 c3 d3
  rw [h0, h1, h2, h3]

private theorem zipAddLane4Shares_spec
    (ls : List Goldilocks) (as bs : List Lane4)
    (ha : as.length = ls.length) (hb : bs.length = ls.length) :
    (zipAddLane4Shares as bs).length = ls.length ∧
    lagrangeCombineLane4 ls (zipAddLane4Shares as bs) =
      lane4Add (lagrangeCombineLane4 ls as) (lagrangeCombineLane4 ls bs) := by
  induction ls generalizing as bs with
  | nil =>
    cases as with
    | nil =>
      cases bs with
      | nil => exact ⟨rfl, by decide⟩
      | cons _ _ => exact absurd hb (by simp only [List.length_cons, List.length_nil]; omega)
    | cons _ _ => exact absurd ha (by simp only [List.length_cons, List.length_nil]; omega)
  | cons l ls ih =>
    cases as with
    | nil => exact absurd ha (by simp only [List.length_cons, List.length_nil]; omega)
    | cons a as =>
      cases bs with
      | nil => exact absurd hb (by simp only [List.length_cons, List.length_nil]; omega)
      | cons b bs =>
        obtain ⟨ihL, ihC⟩ := ih as bs (Nat.succ.inj ha) (Nat.succ.inj hb)
        refine ⟨by simp [zipAddLane4Shares, ihL], ?_⟩
        dsimp only [zipAddLane4Shares, lagrangeCombineLane4]
        rw [ihC, lane4Scale_add_distrib, lane4Add_four_rearrange]

/-- Abstract online shared permutation handle preventing equation-generator WHNF expansion of
    30-round `runSharedPoseidon2PermOnline` inside recursive MPC hypertree definitions. -/
structure CorduroyMpcPermRunner where
  runPerm : List Goldilocks → List Poseidon2State12 → Poseidon2CallPrep → Option (List Poseidon2State12)

def corduroyMpcRunner : CorduroyMpcPermRunner where
  runPerm := fun lambdas ss prep =>
    runSharedPoseidon2PermOnline lambdas ss prep.extInit prep.inter prep.extTerm

private theorem corduroyMpcRunner_eq (lambdas : List Goldilocks) (ss : List Poseidon2State12)
    (prep : Poseidon2CallPrep) :
    corduroyMpcRunner.runPerm lambdas ss prep =
      runSharedPoseidon2PermOnline lambdas ss prep.extInit prep.inter prep.extTerm := by
  unfold corduroyMpcRunner; rfl

attribute [local irreducible] corduroyMpcRunner

/-- Share-level `Poseidon2` evaluation of `corduroyPrfMsg` (`skPrf` remains secret-shared throughout). -/
def mpcCorduroyPrfMsgWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (optRand msg : Lane4) (prep0 prep1 : Poseidon2CallPrep) : Option Lane4 :=
  let n := lambdas.length
  let cap : Lane4 := ⟨corduroyTagHMsgStateless, Goldilocks.zero, Goldilocks.zero, corduroyPoseidon2Iv⟩
  let st0Sh := zipState12Shares sh.skPrfShares (List.replicate n optRand) (List.replicate n cap)
  match mr.runPerm lambdas st0Sh prep0 with
  | none => none
  | some out0Sh =>
    let b0MsgSh := zipAddLane4Shares (out0Sh.map (·.b0)) (List.replicate n msg)
    let st1Sh := zipState12Shares b0MsgSh (out0Sh.map (·.b1)) (out0Sh.map (·.b2))
    match mr.runPerm lambdas st1Sh prep1 with
    | none => none
    | some out1Sh => some (lagrangeCombineLane4 lambdas (out1Sh.map (·.b0)))

/-- Share-level Jive feed-forward step `[val] -> [F(pkSeed, adrs, val)]` keeping chain links secret-shared! -/
def mpcCorduroySharedJiveStepWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks)
    (pkSeed : Lane4) (adrs : CorduroyAdrs) (valSh : List Lane4) (prep : Poseidon2CallPrep) : Option (List Lane4) :=
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap adrs
  let stSh := zipState12Shares valSh (List.replicate n pkSeed) (List.replicate n cap)
  match mr.runPerm lambdas stSh prep with
  | none => none
  | some permSh => some (zipAddLane4Shares (permSh.map (·.b0)) valSh)

def mpcCorduroySharedChainIterWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (pkSeed : Lane4)
    (layer treeIdx kpIdx chainIdx startStep steps : Nat)
    (valSh : List Lane4) (stepPrep : Nat → Poseidon2CallPrep) : Option (List Lane4) :=
  match steps with
  | 0 => some valSh
  | s + 1 =>
    match mpcCorduroySharedJiveStepWith mr lambdas pkSeed
            (wotsStepAdrs layer treeIdx kpIdx chainIdx startStep) valSh (stepPrep startStep) with
    | none => none
    | some nextSh =>
      mpcCorduroySharedChainIterWith mr lambdas pkSeed layer treeIdx kpIdx chainIdx (startStep + 1) s nextSh stepPrep
  termination_by structural steps

/-- Share-level WOTS+C chain evaluation: derives `[c_0]` from `[skSeed]`, advances `steps` links
    in MPC without opening intermediate chain values `< steps`, and opens ONLY `c_steps`! -/
def mpcCorduroyEvalWotsChainEndWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (layer treeIdx kpIdx chainIdx steps : Nat) (callPrep : Nat → Poseidon2CallPrep) : Option Lane4 :=
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (wotsPrfAdrs layer treeIdx kpIdx chainIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  match mr.runPerm lambdas initSh (callPrep 0) with
  | none => none
  | some basePermSh =>
    let baseSh := basePermSh.map (·.b0)
    match mpcCorduroySharedChainIterWith mr lambdas sh.pkSeed layer treeIdx kpIdx chainIdx 0 steps baseSh
            (fun s => callPrep (s + 1)) with
    | none => none
    | some endSh => some (lagrangeCombineLane4 lambdas endSh)

/-- Share-level FORS secret reveal (opened ONLY for the `k` message-selected FORS leaves). -/
def mpcCorduroyEvalForsSecretWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx treeJ leafIdx : Nat) (prep : Poseidon2CallPrep) : Option Lane4 :=
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (forsPrfAdrs leafGlobalIdx treeJ leafIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  match mr.runPerm lambdas initSh prep with
  | none => none
  | some outSh => some (lagrangeCombineLane4 lambdas (outSh.map (·.b0)))

/-- Share-level unrevealed FORS leaf hash: derives `[sec]` in MPC, applies 1 shared Jive step in MPC,
    and opens ONLY the public leaf hash (`sec` is NEVER reconstructed in cleartext!). -/
def mpcCorduroyEvalForsLeafHashWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx treeJ leafIdx : Nat) (prep0 prep1 : Poseidon2CallPrep) : Option Lane4 :=
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (forsPrfAdrs leafGlobalIdx treeJ leafIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  match mr.runPerm lambdas initSh prep0 with
  | none => none
  | some secPermSh =>
    match mpcCorduroySharedJiveStepWith mr lambdas sh.pkSeed (forsLeafAdrs leafGlobalIdx treeJ leafIdx)
            (secPermSh.map (·.b0)) prep1 with
    | none => none
    | some leafSh => some (lagrangeCombineLane4 lambdas leafSh)

private def mapMList {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x with
    | none => none
    | some y =>
      match mapMList f xs with
      | none => none
      | some ys => some (y :: ys)

private theorem mapMList_eq_some_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = some (g x)) → mapMList f xs = some (xs.map g)
  | [], _ => rfl
  | x :: xs, h => by
    dsimp only [mapMList, List.map]
    rw [h x (List.mem_cons_self ..),
        mapMList_eq_some_map f g xs (fun z hz => h z (List.mem_cons_of_mem _ hz))]

/-- Distributed WOTS+C public key computation via share-level `mpcCorduroyEvalWotsChainEndWith` at `steps = 3`. -/
def mpcCorduroyWotsPkWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (layer treeIdx kpIdx : Nat) (callPrep : Nat → Nat → Poseidon2CallPrep) : Option Lane4 :=
  match mapMList (fun c => mpcCorduroyEvalWotsChainEndWith mr lambdas sh layer treeIdx kpIdx c 3 (callPrep c))
          (List.range cfg.wotsChains) with
  | none => none
  | some peaks => some (corduroyWotsPkCompressWith eng sh.pkSeed layer treeIdx kpIdx peaks)

def mpcCorduroySubtreeRootWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (layer treeIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep) : Option Lane4 :=
  match mapMList (fun kp => mpcCorduroyWotsPkWith eng mr cfg lambdas sh layer treeIdx kp (callPrep kp))
          (List.range (2 ^ cfg.subtreeHeight)) with
  | none => none
  | some leaves =>
    some (computeCorduroyMerkleNodeWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx)
      (fun kp => leaves.getD kp lane4Zero) cfg.subtreeHeight 0)

def corduroyThresholdKeygenWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (callPrep : Nat → Nat → Nat → Poseidon2CallPrep) : Option CorduroyPublicKey :=
  match mpcCorduroySubtreeRootWith eng mr cfg lambdas sh (cfg.numLayers - 1) 0 callPrep with
  | none => none
  | some pkRoot => some { pkSeed := sh.pkSeed, pkRoot := pkRoot }

/-- **Dealerless `(t, n)` Shamir/SPDZ Distributed Key Generation (`corduroyThresholdKeygen`)**. -/
def corduroyThresholdKeygen (cfg : CorduroyParams) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (callPrep : Nat → Nat → Nat → Poseidon2CallPrep) : Option CorduroyPublicKey :=
  corduroyThresholdKeygenWith corduroyPoseidon2Engine corduroyMpcRunner cfg lambdas sh callPrep

def mpcCorduroyForsTreeLeavesWith (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx treeJ : Nat) (callPrep : Nat → Nat → Poseidon2CallPrep) : Option (List Lane4) :=
  mapMList (fun u => mpcCorduroyEvalForsLeafHashWith mr lambdas sh leafGlobalIdx treeJ u (callPrep u 0) (callPrep u 1))
    (List.range (2 ^ cfg.forsHeight))

def mpcCorduroyForsPkWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep) : Option Lane4 :=
  match mapMList (fun j =>
          match mpcCorduroyForsTreeLeavesWith mr cfg lambdas sh leafGlobalIdx j (callPrep j) with
          | none => none
          | some leaves =>
            some (computeCorduroyMerkleNodeWith eng sh.pkSeed (forsNodeAdrs leafGlobalIdx j)
              (fun u => leaves.getD u lane4Zero) cfg.forsHeight 0))
          (List.range cfg.forsTrees) with
  | none => none
  | some roots => some (corduroyForsRootsCompressWith eng sh.pkSeed leafGlobalIdx roots)

def mpcCorduroyBuildForsOpeningsWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep)
    (j : Nat) (forsIndices : List Nat) : Option (List CorduroyForsOpening) :=
  match forsIndices with
  | [] => some []
  | idx :: idxs =>
    match mpcCorduroyEvalForsSecretWith mr lambdas sh leafGlobalIdx j idx (callPrep j idx 2),
          mpcCorduroyForsTreeLeavesWith mr cfg lambdas sh leafGlobalIdx j (callPrep j) with
    | some sec, some leaves =>
      let path := buildCorduroyMerklePathWith eng sh.pkSeed (forsNodeAdrs leafGlobalIdx j)
        (fun u => leaves.getD u lane4Zero) cfg.forsHeight 0 idx
      match mpcCorduroyBuildForsOpeningsWith eng mr cfg lambdas sh leafGlobalIdx callPrep (j + 1) idxs with
      | none => none
      | some rest => some ({ secretVal := sec, authPath := path } :: rest)
    | _, _ => none
  termination_by structural forsIndices

def mpcCorduroySignLayersAuxWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (pk : CorduroyPublicKey) (callPrep : Nat → Nat → Nat → Nat → Poseidon2CallPrep)
    (layer remIdx : Nat) (curRoot : Lane4) (ctrs : List Nat) : Option (List CorduroyLayerSig) :=
  match ctrs with
  | [] => some []
  | ctr :: restCtrs =>
    let subLeaves := 2 ^ cfg.subtreeHeight
    let kpIdx := remIdx % subLeaves
    let treeIdx := remIdx / subLeaves
    let hmsg := corduroyLayerHmsgWith eng pk layer treeIdx kpIdx ctr curRoot
    let digits := corduroyExtractDigits cfg.wotsChains hmsg
    match mapMList (fun c =>
            mpcCorduroyEvalWotsChainEndWith mr lambdas sh layer treeIdx kpIdx c (digits[c]!) (callPrep layer kpIdx c))
            (List.range cfg.wotsChains),
          mapMList (fun kp => mpcCorduroyWotsPkWith eng mr cfg lambdas sh layer treeIdx kp (callPrep layer kp))
            (List.range subLeaves) with
    | some chains, some leaves =>
      let leafFn := fun kp => leaves.getD kp lane4Zero
      let path := buildCorduroyMerklePathWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx) leafFn cfg.subtreeHeight 0 kpIdx
      let nextRoot := computeCorduroyMerkleNodeWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx) leafFn cfg.subtreeHeight 0
      match mpcCorduroySignLayersAuxWith eng mr cfg lambdas sh pk callPrep (layer + 1) treeIdx nextRoot restCtrs with
      | none => none
      | some restSigs => some ({ tswCtr := ctr, wotsChains := chains, authPath := path } :: restSigs)
    | _, _ => none
  termination_by structural ctrs

/-- Full preprocessing bundle for a dealerless `(t, n)` Shamir/SPDZ `Corduroy` threshold signing session. -/
structure CorduroyMpcPrep where
  keygenPrep : Nat → Nat → Nat → Poseidon2CallPrep
  prfPrep    : Nat → Poseidon2CallPrep
  forsPrep   : Nat → Nat → Nat → Poseidon2CallPrep
  layerPrep  : Nat → Nat → Nat → Nat → Poseidon2CallPrep

def CorduroyMpcPrep.validAt (lambdas : List Goldilocks) (p : CorduroyMpcPrep) : Prop :=
  (∀ kp c s, (p.keygenPrep kp c s).validAt lambdas) ∧
  (∀ b, (p.prfPrep b).validAt lambdas) ∧
  (∀ j u b, (p.forsPrep j u b).validAt lambdas) ∧
  (∀ l kp c s, (p.layerPrep l kp c s).validAt lambdas)

def corduroyThresholdSignWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks)
    (sh : CorduroyKeyShares) (prep : CorduroyMpcPrep)
    (msg : Lane4) (r : CorduroySignRand) : Option CorduroySig :=
  match corduroyThresholdKeygenWith eng mr cfg lambdas sh prep.keygenPrep with
  | none => none
  | some pk =>
    match mpcCorduroyPrfMsgWith mr lambdas sh r.optRand msg (prep.prfPrep 0) (prep.prfPrep 1) with
    | none => none
    | some rRand =>
      let (leafGlobalIdx, forsIndices, _) := corduroyHashMsgWith eng cfg rRand pk msg
      match mpcCorduroyBuildForsOpeningsWith eng mr cfg lambdas sh leafGlobalIdx prep.forsPrep 0 forsIndices,
            mpcCorduroyForsPkWith eng mr cfg lambdas sh leafGlobalIdx prep.forsPrep with
      | some forsOps, some forsPk =>
        match mpcCorduroySignLayersAuxWith eng mr cfg lambdas sh pk prep.layerPrep 0 leafGlobalIdx forsPk r.layerCtrs with
        | none => none
        | some layerSigs =>
          some { rRand := rRand, forsOpenings := forsOps, layerSigs := layerSigs }
      | _, _ => none

/-- **Dealerless `(t, n)` Shamir/SPDZ Threshold `Corduroy` Signer (`corduroyThresholdSign`)**:
    Evaluates key derivation, `PRF_msg`, FORS openings/trees, and all `d` WOTS+C + Merkle layers
    directly over Shamir shares + SPDZ-MAC-checked `Poseidon2` gates with `0` secret reconstruction. -/
@[expose] def corduroyThresholdSign (cfg : CorduroyParams) (lambdas : List Goldilocks)
    (sh : CorduroyKeyShares) (prep : CorduroyMpcPrep)
    (msg : Lane4) (r : CorduroySignRand) : Option CorduroySig :=
  corduroyThresholdSignWith corduroyPoseidon2Engine corduroyMpcRunner cfg lambdas sh prep msg r

/-- Simulation contract relating a share-level `CorduroyMpcPermRunner` to `CorduroyPermEngine`. -/
def CorduroyMpcSimulates (mr : CorduroyMpcPermRunner) (eng : CorduroyPermEngine)
    (lambdas : List Goldilocks) : Prop :=
  ∀ (stSh : List Poseidon2State12) (prep : Poseidon2CallPrep),
    ringListSum lambdas = Goldilocks.one →
    stSh.length = lambdas.length →
    prep.validAt lambdas →
    ∃ outSh : List Poseidon2State12,
      mr.runPerm lambdas stSh prep = some outSh ∧
      outSh.length = lambdas.length ∧
      lagrangeCombineState12 lambdas outSh = eng.perm (lagrangeCombineState12 lambdas stSh)

private theorem corduroyMpcRunner_simulates_engine (lambdas : List Goldilocks) :
    CorduroyMpcSimulates corduroyMpcRunner corduroyPoseidon2Engine lambdas := by
  intro stSh prep hSum hLen hValid
  obtain ⟨outSh, hRun, hOutLen, hComb⟩ :=
    evalSharedPoseidon2Perm_simulates lambdas stSh prep.extInit prep.inter prep.extTerm
      hSum hLen hValid.1 hValid.2.1 hValid.2.2
  refine ⟨outSh, ?_, hOutLen, ?_⟩
  · rw [corduroyMpcRunner_eq]; exact hRun
  · rw [corduroyPoseidon2Engine_perm]; exact hComb

-- Engine-parametric cut-boundary simulation lemmas (`eng` and `mr` remain free variables, so
-- kernel `isDefEq` never unfolds 30-round `poseidon2Perm12`).
private theorem mpcCorduroyPrfMsgWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (optRand msg : Lane4) (prep0 prep1 : Poseidon2CallPrep)
    (hp0 : prep0.validAt lambdas) (hp1 : prep1.validAt lambdas) :
    mpcCorduroyPrfMsgWith mr lambdas sh optRand msg prep0 prep1 =
      some (corduroyPrfMsgWith eng sk optRand msg) := by
  rcases hMatch with ⟨hSumOne, _, hPrfLen, _, hPrfComb, _⟩
  let n := lambdas.length
  let cap : Lane4 := ⟨corduroyTagHMsgStateless, Goldilocks.zero, Goldilocks.zero, corduroyPoseidon2Iv⟩
  let st0Sh := zipState12Shares sh.skPrfShares (List.replicate n optRand) (List.replicate n cap)
  have hSt0Len : st0Sh.length = n :=
    zipState12Shares_length hPrfLen List.length_replicate List.length_replicate
  obtain ⟨out0Sh, hRun0, hLen0, hComb0⟩ := hSim st0Sh prep0 hSumOne hSt0Len hp0
  have hSt0Comb : lagrangeCombineState12 lambdas st0Sh = ⟨sk.skPrf, optRand, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hPrfLen List.length_replicate List.length_replicate,
        hPrfComb, lagrangeCombineLane4_replicate_public lambdas hSumOne optRand,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hSt0Comb] at hComb0
  obtain ⟨hB0MsgLen, hB0MsgComb⟩ := zipAddLane4Shares_spec lambdas (out0Sh.map (·.b0))
    (List.replicate n msg) (by simp [hLen0]) List.length_replicate
  let b0MsgSh := zipAddLane4Shares (out0Sh.map (·.b0)) (List.replicate n msg)
  let st1Sh := zipState12Shares b0MsgSh (out0Sh.map (·.b1)) (out0Sh.map (·.b2))
  have hSt1Len : st1Sh.length = n :=
    zipState12Shares_length hB0MsgLen (by simp [hLen0, n]) (by simp [hLen0, n])
  obtain ⟨out1Sh, hRun1, _, hComb1⟩ := hSim st1Sh prep1 hSumOne hSt1Len hp1
  have hProj0 := lagrangeCombineState12_proj lambdas out0Sh
  have hSt1Comb : lagrangeCombineState12 lambdas st1Sh =
      ⟨lane4Add (eng.perm ⟨sk.skPrf, optRand, cap⟩).b0 msg,
       (eng.perm ⟨sk.skPrf, optRand, cap⟩).b1,
       (eng.perm ⟨sk.skPrf, optRand, cap⟩).b2⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hB0MsgLen (by simp [hLen0]) (by simp [hLen0]),
        hB0MsgComb, lagrangeCombineLane4_replicate_public lambdas hSumOne msg]
    rw [hComb0] at hProj0
    have hb0 : lagrangeCombineLane4 lambdas (out0Sh.map (·.b0)) = (eng.perm ⟨sk.skPrf, optRand, cap⟩).b0 :=
      (congrArg Poseidon2State12.b0 hProj0).symm
    have hb1 : lagrangeCombineLane4 lambdas (out0Sh.map (·.b1)) = (eng.perm ⟨sk.skPrf, optRand, cap⟩).b1 :=
      (congrArg Poseidon2State12.b1 hProj0).symm
    have hb2 : lagrangeCombineLane4 lambdas (out0Sh.map (·.b2)) = (eng.perm ⟨sk.skPrf, optRand, cap⟩).b2 :=
      (congrArg Poseidon2State12.b2 hProj0).symm
    rw [hb0, hb1, hb2]
  rw [hSt1Comb] at hComb1
  have hProj1 := lagrangeCombineState12_proj lambdas out1Sh
  rw [hComb1] at hProj1
  unfold mpcCorduroyPrfMsgWith corduroyPrfMsgWith
  dsimp only [n, cap, st0Sh]
  rw [hRun0]
  dsimp only [b0MsgSh, st1Sh]
  rw [hRun1]
  dsimp only
  exact congrArg some (congrArg Poseidon2State12.b0 hProj1).symm

private theorem mpcCorduroySharedJiveStepWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (pkSeed : Lane4) (adrs : CorduroyAdrs)
    (valSh : List Lane4) (val : Lane4) (hValLen : valSh.length = lambdas.length)
    (hValComb : lagrangeCombineLane4 lambdas valSh = val)
    (prep : Poseidon2CallPrep) (hPrep : prep.validAt lambdas) :
    ∃ nextSh : List Lane4,
      mpcCorduroySharedJiveStepWith mr lambdas pkSeed adrs valSh prep = some nextSh ∧
      nextSh.length = lambdas.length ∧
      lagrangeCombineLane4 lambdas nextSh =
        lane4Add (eng.perm ⟨val, pkSeed, corduroyEncodeAdrsCap adrs⟩).b0 val := by
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap adrs
  let stSh := zipState12Shares valSh (List.replicate n pkSeed) (List.replicate n cap)
  have hStLen : stSh.length = n :=
    zipState12Shares_length hValLen List.length_replicate List.length_replicate
  obtain ⟨permSh, hRun, hPermLen, hPermComb⟩ := hSim stSh prep hSumOne hStLen hPrep
  have hStComb : lagrangeCombineState12 lambdas stSh = ⟨val, pkSeed, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hValLen List.length_replicate List.length_replicate,
        hValComb, lagrangeCombineLane4_replicate_public lambdas hSumOne pkSeed,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hStComb] at hPermComb
  obtain ⟨hNextLen, hNextComb⟩ := zipAddLane4Shares_spec lambdas (permSh.map (·.b0)) valSh
    (by simp [hPermLen]) hValLen
  have hProj := lagrangeCombineState12_proj lambdas permSh
  rw [hPermComb] at hProj
  have hb0 : lagrangeCombineLane4 lambdas (permSh.map (·.b0)) =
      (eng.perm ⟨val, pkSeed, cap⟩).b0 := (congrArg Poseidon2State12.b0 hProj).symm
  refine ⟨zipAddLane4Shares (permSh.map (·.b0)) valSh, ?_, hNextLen, ?_⟩
  · unfold mpcCorduroySharedJiveStepWith
    dsimp only [n, cap, stSh]
    rw [hRun]
  · rw [hNextComb, hb0, hValComb]

private theorem mpcCorduroySharedChainIterWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx : Nat)
    (steps startStep : Nat) (valSh : List Lane4) (val : Lane4) (stepPrep : Nat → Poseidon2CallPrep)
    (hLen : valSh.length = lambdas.length)
    (hComb : lagrangeCombineLane4 lambdas valSh = val)
    (hPrep : ∀ s, (stepPrep s).validAt lambdas) :
    ∃ endSh : List Lane4,
      mpcCorduroySharedChainIterWith mr lambdas pkSeed layer treeIdx kpIdx chainIdx startStep steps valSh stepPrep = some endSh ∧
      endSh.length = lambdas.length ∧
      lagrangeCombineLane4 lambdas endSh =
        corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx startStep steps val := by
  induction steps generalizing startStep valSh val with
  | zero => exact ⟨valSh, rfl, hLen, hComb⟩
  | succ steps ih =>
    obtain ⟨nextSh, hJive, hNextLen, hNextComb⟩ :=
      mpcCorduroySharedJiveStepWith_eq eng mr lambdas hSim hSumOne pkSeed
        (wotsStepAdrs layer treeIdx kpIdx chainIdx startStep) valSh val hLen hComb
        (stepPrep startStep) (hPrep startStep)
    have hStepEq : lane4Add (eng.perm ⟨val, pkSeed,
        corduroyEncodeAdrsCap (wotsStepAdrs layer treeIdx kpIdx chainIdx startStep)⟩).b0 val =
        corduroyWotsStepWith eng pkSeed layer treeIdx kpIdx chainIdx startStep val := by
      rw [corduroyWotsStepWith_eq]
      exact (corduroySpongeEvalWith_jive_wots eng pkSeed layer treeIdx kpIdx chainIdx startStep val).symm
    rw [hStepEq] at hNextComb
    obtain ⟨endSh, hRest, hEndLen, hEndComb⟩ :=
      ih (startStep + 1) nextSh _ hNextLen hNextComb
    refine ⟨endSh, ?_, hEndLen, hEndComb⟩
    dsimp only [mpcCorduroySharedChainIterWith]
    rw [hJive]
    exact hRest

private theorem mpcCorduroyEvalWotsChainEndWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (layer treeIdx kpIdx chainIdx steps : Nat) (callPrep : Nat → Poseidon2CallPrep)
    (hPrep : ∀ s, (callPrep s).validAt lambdas) :
    mpcCorduroyEvalWotsChainEndWith mr lambdas sh layer treeIdx kpIdx chainIdx steps callPrep =
      some (corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx 0 steps
              (corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx)) := by
  rcases hMatch with ⟨hSumOne, hSeedLen, _, hSeedComb, _, hPkSeedEq⟩
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (wotsPrfAdrs layer treeIdx kpIdx chainIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  have hInitLen : initSh.length = n :=
    zipState12Shares_length hSeedLen List.length_replicate List.length_replicate
  obtain ⟨basePermSh, hRun0, hBaseLen, hBaseComb⟩ := hSim initSh (callPrep 0) hSumOne hInitLen (hPrep 0)
  have hInitComb : lagrangeCombineState12 lambdas initSh = ⟨sk.skSeed, sk.pkSeed, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hSeedLen List.length_replicate List.length_replicate,
        hSeedComb, hPkSeedEq,
        lagrangeCombineLane4_replicate_public lambdas hSumOne sk.pkSeed,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hInitComb] at hBaseComb
  have hProj := lagrangeCombineState12_proj lambdas basePermSh
  rw [hBaseComb] at hProj
  have hb0 : lagrangeCombineLane4 lambdas (basePermSh.map (·.b0)) =
      corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx :=
    (congrArg Poseidon2State12.b0 hProj).symm
  obtain ⟨endSh, hIter, _, hEndComb⟩ :=
    mpcCorduroySharedChainIterWith_eq eng mr lambdas hSim hSumOne sh.pkSeed layer treeIdx kpIdx chainIdx
      steps 0 (basePermSh.map (·.b0))
      (corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx)
      (fun s => callPrep (s + 1)) (by simp [hBaseLen]) hb0 (fun s => hPrep (s + 1))
  unfold mpcCorduroyEvalWotsChainEndWith
  dsimp only [n, cap, initSh]
  rw [hRun0]
  dsimp only
  rw [hIter]
  dsimp only
  rw [hEndComb, hPkSeedEq]

private theorem mpcCorduroyEvalForsSecretWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx treeJ leafIdx : Nat) (prep : Poseidon2CallPrep) (hPrep : prep.validAt lambdas) :
    mpcCorduroyEvalForsSecretWith mr lambdas sh leafGlobalIdx treeJ leafIdx prep =
      some (corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx) := by
  rcases hMatch with ⟨hSumOne, hSeedLen, _, hSeedComb, _, hPkSeedEq⟩
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (forsPrfAdrs leafGlobalIdx treeJ leafIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  have hInitLen : initSh.length = n :=
    zipState12Shares_length hSeedLen List.length_replicate List.length_replicate
  obtain ⟨outSh, hRun, _, hComb⟩ := hSim initSh prep hSumOne hInitLen hPrep
  have hInitComb : lagrangeCombineState12 lambdas initSh = ⟨sk.skSeed, sk.pkSeed, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hSeedLen List.length_replicate List.length_replicate,
        hSeedComb, hPkSeedEq,
        lagrangeCombineLane4_replicate_public lambdas hSumOne sk.pkSeed,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hInitComb] at hComb
  have hProj := lagrangeCombineState12_proj lambdas outSh
  rw [hComb] at hProj
  unfold mpcCorduroyEvalForsSecretWith corduroyForsSecretWith
  dsimp only [n, cap, initSh]
  rw [hRun]
  exact congrArg some (congrArg Poseidon2State12.b0 hProj).symm

private theorem mpcCorduroyEvalForsLeafHashWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx treeJ leafIdx : Nat) (prep0 prep1 : Poseidon2CallPrep)
    (hp0 : prep0.validAt lambdas) (hp1 : prep1.validAt lambdas) :
    mpcCorduroyEvalForsLeafHashWith mr lambdas sh leafGlobalIdx treeJ leafIdx prep0 prep1 =
      some (corduroyHonestForsLeafWith eng sk leafGlobalIdx treeJ leafIdx) := by
  rcases hMatch with ⟨hSumOne, hSeedLen, _, hSeedComb, _, hPkSeedEq⟩
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (forsPrfAdrs leafGlobalIdx treeJ leafIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  have hInitLen : initSh.length = n :=
    zipState12Shares_length hSeedLen List.length_replicate List.length_replicate
  obtain ⟨secPermSh, hRun0, hSecLen, hSecComb⟩ := hSim initSh prep0 hSumOne hInitLen hp0
  have hInitComb : lagrangeCombineState12 lambdas initSh = ⟨sk.skSeed, sk.pkSeed, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hSeedLen List.length_replicate List.length_replicate,
        hSeedComb, hPkSeedEq,
        lagrangeCombineLane4_replicate_public lambdas hSumOne sk.pkSeed,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hInitComb] at hSecComb
  have hProj := lagrangeCombineState12_proj lambdas secPermSh
  rw [hSecComb] at hProj
  have hb0 : lagrangeCombineLane4 lambdas (secPermSh.map (·.b0)) =
      corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx :=
    (congrArg Poseidon2State12.b0 hProj).symm
  obtain ⟨leafSh, hJive, _, hLeafComb⟩ :=
    mpcCorduroySharedJiveStepWith_eq eng mr lambdas hSim hSumOne sh.pkSeed
      (forsLeafAdrs leafGlobalIdx treeJ leafIdx) (secPermSh.map (·.b0))
      (corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx)
      (by simp [hSecLen]) hb0 prep1 hp1
  unfold mpcCorduroyEvalForsLeafHashWith
  dsimp only [n, cap, initSh]
  rw [hRun0]
  dsimp only
  rw [hJive]
  dsimp only
  rw [hLeafComb, hPkSeedEq]
  exact congrArg some (by
    unfold corduroyHonestForsLeafWith corduroyForsLeafHashWith forsLeafAdrs
    exact (corduroySpongeEvalWith_jive_fors eng sk.pkSeed leafGlobalIdx treeJ leafIdx
      (corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx)).symm)

private theorem computeCorduroyMerkleNodeWith_congr_in_range (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (mkAdrs : Nat → Nat → CorduroyAdrs) (f g : Nat → Lane4) :
    ∀ (h idx : Nat),
      (∀ u, u < 2 ^ h * (idx + 1) → f u = g u) →
      computeCorduroyMerkleNodeWith eng pkSeed mkAdrs f h idx =
      computeCorduroyMerkleNodeWith eng pkSeed mkAdrs g h idx
  | 0, idx, hEq => hEq idx (by simp)
  | h + 1, idx, hEq => by
    dsimp only [computeCorduroyMerkleNodeWith]
    have hL : ∀ u, u < 2 ^ h * (2 * idx + 1) → u < 2 ^ (h + 1) * (idx + 1) := by
      intro u hu
      rw [Nat.pow_succ, Nat.mul_assoc]
      exact Nat.lt_of_lt_of_le hu (Nat.mul_le_mul_left (2 ^ h) (by omega))
    have hR : ∀ u, u < 2 ^ h * (2 * idx + 1 + 1) → u < 2 ^ (h + 1) * (idx + 1) := by
      intro u hu
      rw [Nat.pow_succ, Nat.mul_assoc]
      exact Nat.lt_of_lt_of_le hu (Nat.mul_le_mul_left (2 ^ h) (by omega))
    rw [computeCorduroyMerkleNodeWith_congr_in_range eng pkSeed mkAdrs f g h (2 * idx) (fun u hu => hEq u (hL u hu)),
        computeCorduroyMerkleNodeWith_congr_in_range eng pkSeed mkAdrs f g h (2 * idx + 1) (fun u hu => hEq u (hR u hu))]

private theorem buildCorduroyMerklePathWith_congr_in_range (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (mkAdrs : Nat → Nat → CorduroyAdrs) (f g : Nat → Lane4) :
    ∀ (rem lvl idx : Nat),
      idx < 2 ^ rem →
      (∀ u, u < 2 ^ (lvl + rem) → f u = g u) →
      buildCorduroyMerklePathWith eng pkSeed mkAdrs f rem lvl idx =
      buildCorduroyMerklePathWith eng pkSeed mkAdrs g rem lvl idx
  | 0, _, _, _, _ => rfl
  | rem + 1, lvl, idx, hIdxLt, hEq => by
    dsimp only [buildCorduroyMerklePathWith]
    let sibIdx := if idx % 2 == 0 then idx + 1 else idx - 1
    have hSibBound : sibIdx + 1 ≤ 2 ^ (rem + 1) := by
      dsimp only [sibIdx]
      rcases Nat.mod_two_eq_zero_or_one idx with hE | hO
      · rw [Nat.pow_succ] at hIdxLt ⊢; simp [hE]; omega
      · have hNe : (idx % 2 == 0) = false := by rw [hO]; decide
        rw [Nat.pow_succ] at hIdxLt ⊢; simp [hNe]; omega
    have hNodeEq : computeCorduroyMerkleNodeWith eng pkSeed mkAdrs f lvl sibIdx =
        computeCorduroyMerkleNodeWith eng pkSeed mkAdrs g lvl sibIdx := by
      apply computeCorduroyMerkleNodeWith_congr_in_range
      intro u hu
      apply hEq
      have hMul : 2 ^ lvl * (sibIdx + 1) ≤ 2 ^ lvl * 2 ^ (rem + 1) := Nat.mul_le_mul_left _ hSibBound
      rw [← Nat.pow_add] at hMul
      omega
    have hDivLt : idx / 2 < 2 ^ rem := by rw [Nat.pow_succ] at hIdxLt; omega
    have hShift : (lvl + 1) + rem = lvl + (rem + 1) := by omega
    rw [hNodeEq, buildCorduroyMerklePathWith_congr_in_range eng pkSeed mkAdrs f g rem (lvl + 1) (idx / 2) hDivLt
          (by rw [hShift]; exact hEq)]

private theorem getD_map_range {α : Type} (f : Nat → α) (d : α) (n u : Nat) (hu : u < n) :
    ((List.range n).map f).getD u d = f u := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu]
  rfl

private theorem mpcCorduroyWotsPkWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (layer treeIdx kpIdx : Nat) (callPrep : Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ c s, (callPrep c s).validAt lambdas) :
    mpcCorduroyWotsPkWith eng mr cfg lambdas sh layer treeIdx kpIdx callPrep =
      some (corduroyHonestWotsPkWith eng cfg sk layer treeIdx kpIdx) := by
  unfold mpcCorduroyWotsPkWith corduroyHonestWotsPkWith corduroyHonestWotsPeaksWith
  rw [mapMList_eq_some_map _ _ (List.range cfg.wotsChains)
        (fun c _ => mpcCorduroyEvalWotsChainEndWith_eq eng mr lambdas hSim sh sk hMatch layer treeIdx kpIdx c 3
          (callPrep c) (hPrep c))]
  dsimp only
  rw [hMatch.2.2.2.2.2]

private theorem mpcCorduroySubtreeRootWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (layer treeIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ kp c s, (callPrep kp c s).validAt lambdas) :
    mpcCorduroySubtreeRootWith eng mr cfg lambdas sh layer treeIdx callPrep =
      some (corduroyHonestSubtreeRootWith eng cfg sk layer treeIdx) := by
  unfold mpcCorduroySubtreeRootWith corduroyHonestSubtreeRootWith
  rw [mapMList_eq_some_map _ _ (List.range (2 ^ cfg.subtreeHeight))
        (fun kp _ => mpcCorduroyWotsPkWith_eq eng mr cfg lambdas hSim sh sk hMatch layer treeIdx kp (callPrep kp) (hPrep kp))]
  dsimp only
  rw [hMatch.2.2.2.2.2]
  congr 1
  apply computeCorduroyMerkleNodeWith_congr_in_range
  intro u hu
  simp only [Nat.zero_add, Nat.mul_one] at hu
  exact getD_map_range _ _ _ u hu

private theorem mpcCorduroyForsTreeLeavesWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx treeJ : Nat) (callPrep : Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ u b, (callPrep u b).validAt lambdas) :
    mpcCorduroyForsTreeLeavesWith mr cfg lambdas sh leafGlobalIdx treeJ callPrep =
      some ((List.range (2 ^ cfg.forsHeight)).map
        (corduroyHonestForsLeafWith eng sk leafGlobalIdx treeJ)) :=
  mapMList_eq_some_map _ _ (List.range (2 ^ cfg.forsHeight))
    (fun u _ => mpcCorduroyEvalForsLeafHashWith_eq eng mr lambdas hSim sh sk hMatch leafGlobalIdx treeJ u
      (callPrep u 0) (callPrep u 1) (hPrep u 0) (hPrep u 1))

private theorem mpcCorduroyForsPkWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ j u b, (callPrep j u b).validAt lambdas) :
    mpcCorduroyForsPkWith eng mr cfg lambdas sh leafGlobalIdx callPrep =
      some (corduroyHonestForsPkWith eng cfg sk leafGlobalIdx) := by
  unfold mpcCorduroyForsPkWith corduroyHonestForsPkWith
  rw [mapMList_eq_some_map _ (corduroyHonestForsTreeRootWith eng cfg sk leafGlobalIdx)
        (List.range cfg.forsTrees) ?_]
  · dsimp only; rw [hMatch.2.2.2.2.2]
  · intro j _
    rw [mpcCorduroyForsTreeLeavesWith_eq eng mr cfg lambdas hSim sh sk hMatch leafGlobalIdx j (callPrep j) (hPrep j)]
    dsimp only
    rw [hMatch.2.2.2.2.2]
    congr 1
    unfold corduroyHonestForsTreeRootWith
    apply computeCorduroyMerkleNodeWith_congr_in_range
    intro u hu
    simp only [Nat.zero_add, Nat.mul_one] at hu
    exact getD_map_range _ _ _ u hu

private theorem mpcCorduroyBuildForsOpeningsWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ j u b, (callPrep j u b).validAt lambdas)
    (idxs : List Nat) (startJ : Nat)
    (hB : ∀ idx ∈ idxs, idx < 2 ^ cfg.forsHeight) :
    mpcCorduroyBuildForsOpeningsWith eng mr cfg lambdas sh leafGlobalIdx callPrep startJ idxs =
      some (corduroyBuildForsOpeningsWith eng cfg sk leafGlobalIdx startJ idxs) := by
  induction idxs generalizing startJ with
  | nil => rfl
  | cons idx idxs ih =>
    have hIdxLt : idx < 2 ^ cfg.forsHeight := hB idx (List.mem_cons_self ..)
    have hTailB : ∀ x ∈ idxs, x < 2 ^ cfg.forsHeight := fun x hx => hB x (List.mem_cons_of_mem _ hx)
    dsimp only [mpcCorduroyBuildForsOpeningsWith, corduroyBuildForsOpeningsWith]
    rw [mpcCorduroyEvalForsSecretWith_eq eng mr lambdas hSim sh sk hMatch leafGlobalIdx startJ idx _ (hPrep startJ idx 2),
        mpcCorduroyForsTreeLeavesWith_eq eng mr cfg lambdas hSim sh sk hMatch leafGlobalIdx startJ _ (hPrep startJ),
        ih (startJ + 1) hTailB]
    dsimp only
    rw [hMatch.2.2.2.2.2]
    congr 2
    congr 1
    apply buildCorduroyMerklePathWith_congr_in_range _ _ _ _ _ cfg.forsHeight 0 idx hIdxLt
    intro u hu
    rw [Nat.zero_add] at hu
    exact getD_map_range _ _ _ u hu

private theorem mpcCorduroySignLayersAuxWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (pk : CorduroyPublicKey) (callPrep : Nat → Nat → Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ l kp c s, (callPrep l kp c s).validAt lambdas)
    (ctrs : List Nat) (layer remIdx : Nat) (curRoot : Lane4) :
    mpcCorduroySignLayersAuxWith eng mr cfg lambdas sh pk callPrep layer remIdx curRoot ctrs =
      some (corduroySignLayersAuxWith eng cfg sk pk layer remIdx curRoot ctrs) := by
  induction ctrs generalizing layer remIdx curRoot with
  | nil => rfl
  | cons ctr restCtrs ih =>
    dsimp only [mpcCorduroySignLayersAuxWith, corduroySignLayersAuxWith]
    let subLeaves := 2 ^ cfg.subtreeHeight
    let kpIdx := remIdx % subLeaves
    let treeIdx := remIdx / subLeaves
    have hKpLt : kpIdx < subLeaves := Nat.mod_lt _ (Nat.two_pow_pos _)
    let hmsg := corduroyLayerHmsgWith eng pk layer treeIdx kpIdx ctr curRoot
    let digits := corduroyExtractDigits cfg.wotsChains hmsg
    rw [mapMList_eq_some_map _
          (fun c => corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx c 0 (digits[c]!)
            (corduroyWotsSecretWith eng sk layer treeIdx kpIdx c))
          (List.range cfg.wotsChains)
          (fun c _ => mpcCorduroyEvalWotsChainEndWith_eq eng mr lambdas hSim sh sk hMatch layer treeIdx kpIdx c
            (digits[c]!) (callPrep layer kpIdx c) (hPrep layer kpIdx c)),
        mapMList_eq_some_map _ (corduroyHonestWotsPkWith eng cfg sk layer treeIdx)
          (List.range subLeaves)
          (fun kp _ => mpcCorduroyWotsPkWith_eq eng mr cfg lambdas hSim sh sk hMatch layer treeIdx kp
            (callPrep layer kp) (hPrep layer kp))]
    dsimp only
    have hNextRootEq :
        computeCorduroyMerkleNodeWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx)
          (fun kp => ((List.range subLeaves).map
            (corduroyHonestWotsPkWith eng cfg sk layer treeIdx)).getD kp lane4Zero)
          cfg.subtreeHeight 0 =
        corduroyHonestSubtreeRootWith eng cfg sk layer treeIdx := by
      rw [hMatch.2.2.2.2.2]
      unfold corduroyHonestSubtreeRootWith
      apply computeCorduroyMerkleNodeWith_congr_in_range
      intro u hu
      simp only [Nat.zero_add, Nat.mul_one] at hu
      exact getD_map_range _ _ _ u hu
    have hPathEq :
        buildCorduroyMerklePathWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx)
          (fun kp => ((List.range subLeaves).map
            (corduroyHonestWotsPkWith eng cfg sk layer treeIdx)).getD kp lane4Zero)
          cfg.subtreeHeight 0 kpIdx =
        buildCorduroyMerklePathWith eng sk.pkSeed (xmssMerkleAdrs layer treeIdx)
          (corduroyHonestWotsPkWith eng cfg sk layer treeIdx) cfg.subtreeHeight 0 kpIdx := by
      rw [hMatch.2.2.2.2.2]
      apply buildCorduroyMerklePathWith_congr_in_range _ _ _ _ _ cfg.subtreeHeight 0 kpIdx hKpLt
      intro u hu
      rw [Nat.zero_add] at hu
      exact getD_map_range _ _ _ u hu
    rw [hNextRootEq, hPathEq,
        ih (layer + 1) treeIdx (corduroyHonestSubtreeRootWith eng cfg sk layer treeIdx)]

private theorem corduroy_threshold_matches_standalone_with
    (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks)
    (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey)
    (prep : CorduroyMpcPrep) (msg : Lane4) (r : CorduroySignRand)
    (hMatch : sh.MatchesSecret lambdas sk)
    (hPrep : prep.validAt lambdas) :
    corduroyThresholdKeygenWith eng mr cfg lambdas sh prep.keygenPrep = some (corduroyDerivePkWith eng cfg sk) ∧
    corduroyThresholdSignWith eng mr cfg lambdas sh prep msg r = some (corduroySignWith eng cfg sk msg r) ∧
    (CorduroyValidGrindWith eng cfg sk msg r →
      corduroyVerifyWith eng cfg (corduroyDerivePkWith eng cfg sk) msg (corduroySignWith eng cfg sk msg r) = true) := by
  rcases hPrep with ⟨hKgPrep, hPrfPrep, hForsPrep, hLayPrep⟩
  have hKg : corduroyThresholdKeygenWith eng mr cfg lambdas sh prep.keygenPrep = some (corduroyDerivePkWith eng cfg sk) := by
    unfold corduroyThresholdKeygenWith corduroyDerivePkWith
    rw [mpcCorduroySubtreeRootWith_eq eng mr cfg lambdas hSim sh sk hMatch (cfg.numLayers - 1) 0 prep.keygenPrep hKgPrep]
    dsimp only
    rw [hMatch.2.2.2.2.2]
  refine ⟨hKg, ?_, corduroyVerifyWith_corduroySignWith eng cfg sk msg r⟩
  unfold corduroyThresholdSignWith corduroySignWith
  rw [hKg]
  dsimp only
  rw [mpcCorduroyPrfMsgWith_eq eng mr lambdas hSim sh sk hMatch r.optRand msg (prep.prfPrep 0) (prep.prfPrep 1)
        (hPrfPrep 0) (hPrfPrep 1)]
  dsimp only
  let pk := corduroyDerivePkWith eng cfg sk
  let rRand := corduroyPrfMsgWith eng sk r.optRand msg
  obtain ⟨_, _, hForsIdxBounds⟩ := corduroyHashMsgWith_bounds eng cfg rRand pk msg
  rw [mpcCorduroyBuildForsOpeningsWith_eq eng mr cfg lambdas hSim sh sk hMatch _ prep.forsPrep hForsPrep _ 0 hForsIdxBounds,
      mpcCorduroyForsPkWith_eq eng mr cfg lambdas hSim sh sk hMatch _ prep.forsPrep hForsPrep]
  dsimp only
  rw [mpcCorduroySignLayersAuxWith_eq eng mr cfg lambdas hSim sh sk hMatch pk prep.layerPrep hLayPrep]

/-- **Theorem 1: `Corduroy` Dealerless Threshold Matched-Input Bit-Identity & Completeness
    (`corduroy_threshold_matches_standalone`)**:
    For ANY `(t, n)` Shamir secret sharing `sh` of `sk = (skSeed, skPrf, pkSeed)` over `Goldilocks`
    and valid SPDZ-MAC-authenticated `Poseidon2` preprocessing `prep`:
    1. Distributed keygen `corduroyThresholdKeygen` outputs `some (corduroyDerivePk cfg sk)`;
    2. Distributed threshold signing `corduroyThresholdSign` outputs `some (corduroySign cfg sk msg r)`
       (**bit-for-bit identical** to standalone `corduroySign` under matched `(sk, msg, r)`, while
       never reconstructing `skSeed`, `skPrf`, unrevealed chain links, or unrevealed FORS leaves);
    3. Under any valid counter schedule `CorduroyValidGrind cfg sk msg r`, both standalone and
       threshold outputs satisfy `corduroyVerify = true`. -/
theorem corduroy_threshold_matches_standalone
    (cfg : CorduroyParams) (lambdas : List Goldilocks)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey)
    (prep : CorduroyMpcPrep) (msg : Lane4) (r : CorduroySignRand)
    (hMatch : sh.MatchesSecret lambdas sk)
    (hPrep : prep.validAt lambdas) :
    corduroyThresholdKeygen cfg lambdas sh prep.keygenPrep = some (corduroyDerivePk cfg sk) ∧
    corduroyThresholdSign cfg lambdas sh prep msg r = some (corduroySign cfg sk msg r) ∧
    (CorduroyValidGrind cfg sk msg r →
      corduroyVerify cfg (corduroyDerivePk cfg sk) msg (corduroySign cfg sk msg r) = true) :=
  corduroy_threshold_matches_standalone_with corduroyPoseidon2Engine corduroyMpcRunner
    cfg lambdas (corduroyMpcRunner_simulates_engine lambdas) sh sk prep msg r hMatch hPrep

/-! ## §2. Constructive `Corduroy` Multi-Target EUF-CMA Witness Extractor (`corduroy_euf_cma_extract`) -/

/-- Constructively locate the first coordinate `idx` where two equal-length lists differ (`0 Classical.choice`). -/
def findListDiffCoord {α : Type} [DecidableEq α] (xs ys : List α)
    (hLen : xs.length = ys.length) (hNe : xs ≠ ys) :
    { idx : Nat // ∃ (h1 : idx < xs.length) (h2 : idx < ys.length), xs[idx]'h1 ≠ ys[idx]'h2 } :=
  match xs, ys with
  | [], [] => False.elim (hNe rfl)
  | _ :: _, [] => False.elim (Nat.succ_ne_zero _ hLen)
  | [], _ :: _ => False.elim (Nat.succ_ne_zero _ hLen.symm)
  | x :: xs', y :: ys' =>
    if hxy : x = y then
      have hTailNe : xs' ≠ ys' := fun hEq => hNe (by rw [hxy, hEq])
      let ⟨i, hi⟩ := findListDiffCoord xs' ys' (Nat.succ.inj hLen) hTailNe
      ⟨i + 1, by
        rcases hi with ⟨h1, h2, hDiff⟩
        exact ⟨Nat.succ_lt_succ h1, Nat.succ_lt_succ h2, by simpa using hDiff⟩⟩
    else
      ⟨0, ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _, by simpa using hxy⟩⟩
termination_by structural xs

/-- **Constructive Target-Sum Conservation Extractor (`findSmallerDigitCoord`)**:
    Given `dsStar ≠ dsHon` of equal length with `natListSum dsStar ≤ natListSum dsHon`,
    constructively (`0 Classical.choice`) extracts a coordinate `idx` with `dsStar[idx] < dsHon[idx]`. -/
def findSmallerDigitCoord (dsStar dsHon : List Nat)
    (hLen : dsStar.length = dsHon.length) (hNe : dsStar ≠ dsHon)
    (hSum : natListSum dsStar ≤ natListSum dsHon) :
    { idx : Nat // ∃ (h1 : idx < dsStar.length) (h2 : idx < dsHon.length), dsStar[idx]'h1 < dsHon[idx]'h2 } :=
  match dsStar, dsHon with
  | [], [] => False.elim (hNe rfl)
  | _ :: _, [] => False.elim (Nat.succ_ne_zero _ hLen)
  | [], _ :: _ => False.elim (Nat.succ_ne_zero _ hLen.symm)
  | x :: xs, y :: ys =>
    if hlt : x < y then
      ⟨0, ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _, by simpa using hlt⟩⟩
    else
      have hTailNe : xs ≠ ys := fun hEq => by
        have hxEq : x = y := by
          dsimp only [natListSum] at hSum
          rw [hEq] at hSum
          omega
        exact hNe (by rw [hxEq, hEq])
      have hTailSum : natListSum xs ≤ natListSum ys := by
        dsimp only [natListSum] at hSum
        omega
      let ⟨i, hi⟩ := findSmallerDigitCoord xs ys (Nat.succ.inj hLen) hTailNe hTailSum
      ⟨i + 1, by
        rcases hi with ⟨h1, h2, hDiff⟩
        exact ⟨Nat.succ_lt_succ h1, Nat.succ_lt_succ h2, by simpa using hDiff⟩⟩
termination_by structural dsStar

/-- **WOTS+C Reused-Keypair Target-Sum Conservation (`wotsTargetSum_reused_smaller_digit`)**:
    On any reused WOTS+C keypair with distinct digit vectors `dsStar ≠ dsHon` having equal sum
    `targetSum`, there constructively exists a chain coordinate `idx` with `dsStar[idx] < dsHon[idx]`. -/
def wotsTargetSum_reused_smaller_digit (targetSum : Nat) (dsStar dsHon : List Nat)
    (hLen : dsStar.length = dsHon.length) (hNe : dsStar ≠ dsHon)
    (hSumStar : natListSum dsStar = targetSum) (hSumHon : natListSum dsHon = targetSum) :
    { idx : Nat // ∃ (h1 : idx < dsStar.length) (h2 : idx < dsHon.length), dsStar[idx]'h1 < dsHon[idx]'h2 } :=
  findSmallerDigitCoord dsStar dsHon hLen hNe (by omega)

private theorem natListSum_replicate (n k : Nat) :
    natListSum (List.replicate n k) = k * n := by
  induction n with
  | zero => simp [natListSum]
  | succ n ih =>
    simp only [List.replicate_succ, natListSum, ih]
    rw [Nat.mul_succ, Nat.add_comm]

/-- Constructively extract a bounded witness `k < n` for a decidable predicate `P` (`0 Classical.choice`). -/
def findBoundedDecidableWitness (P : Nat → Prop) [∀ k, Decidable (P k)] :
    ∀ (n : Nat), (∃ k, k < n ∧ P k) → { k : Nat // k < n ∧ P k }
  | 0, hEx => False.elim (by rcases hEx with ⟨_, hk, _⟩; exact Nat.not_lt_zero _ hk)
  | n + 1, hEx =>
    if hPn : P n then
      ⟨n, ⟨Nat.lt_succ_self n, hPn⟩⟩
    else
      have hPrev : ∃ k, k < n ∧ P k := by
        rcases hEx with ⟨k, hkLt, hPk⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hkLt with hkLt' | rfl
        · exact ⟨k, hkLt', hPk⟩
        · exact False.elim (hPn hPk)
      let ⟨k, hkLt, hPk⟩ := findBoundedDecidableWitness P n hPrev
      ⟨k, ⟨Nat.lt_succ_of_lt hkLt, hPk⟩⟩

/-- Engine-parametric message-hash collision witness. -/
structure CorduroyMsgHashCollisionWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) where
  r1             : Lane4
  pk1            : CorduroyPublicKey
  msg1           : Lane4
  r2             : Lane4
  pk2            : CorduroyPublicKey
  msg2           : Lane4
  distinctInputs : (r1, pk1, msg1) ≠ (r2, pk2, msg2)
  sameLeafIdx    : (corduroyHashMsgWith eng cfg r1 pk1 msg1).1 = (corduroyHashMsgWith eng cfg r2 pk2 msg2).1
  sameMsgDigest  : (corduroyHashMsgWith eng cfg r1 pk1 msg1).2.1 = (corduroyHashMsgWith eng cfg r2 pk2 msg2).2.1

/-- **`Corduroy` Message-Hash Collision Witness (`CorduroyMsgHashCollision`)**:
    Distinct `(R, pk, msg) ≠ (R', pk', msg')` mapping under `corduroyHashMsg` to the exact same
    hypertree leaf index AND `k`-tree FORS message digest. -/
structure CorduroyMsgHashCollision (cfg : CorduroyParams) where
  r1             : Lane4
  pk1            : CorduroyPublicKey
  msg1           : Lane4
  r2             : Lane4
  pk2            : CorduroyPublicKey
  msg2           : Lane4
  distinctInputs : (r1, pk1, msg1) ≠ (r2, pk2, msg2)
  sameLeafIdx    : (corduroyHashMsg cfg r1 pk1 msg1).1 = (corduroyHashMsg cfg r2 pk2 msg2).1
  sameMsgDigest  : (corduroyHashMsg cfg r1 pk1 msg1).2.1 = (corduroyHashMsg cfg r2 pk2 msg2).2.1

/-- Engine-parametric tweakable `Poseidon2` sponge collision witness. -/
structure CorduroySpongeTweakCollisionWith (eng : CorduroyPermEngine) (pkSeed : Lane4) where
  adrs1                : CorduroyAdrs
  in1                  : List Lane4
  adrs2                : CorduroyAdrs
  in2                  : List Lane4
  distinctTweakOrInput : (adrs1, in1) ≠ (adrs2, in2)
  sameSpongeOutput     : corduroySpongeEvalWith eng pkSeed adrs1 in1 = corduroySpongeEvalWith eng pkSeed adrs2 in2

/-- **`Corduroy` Tweakable Sponge Collision Witness (`CorduroySpongeTweakCollision`)**:
    Distinct `(adrs1, in1) ≠ (adrs2, in2)` producing the identical 4-Goldilocks-limb `Lane4`
    sponge output along the hypertree, FORS, `H_msg`, or WOTS+C `T_ℓ` compression. -/
structure CorduroySpongeTweakCollision (pkSeed : Lane4) where
  adrs1                : CorduroyAdrs
  in1                  : List Lane4
  adrs2                : CorduroyAdrs
  in2                  : List Lane4
  distinctTweakOrInput : (adrs1, in1) ≠ (adrs2, in2)
  sameSpongeOutput     : corduroySpongeEval pkSeed adrs1 in1 = corduroySpongeEval pkSeed adrs2 in2

/-- Engine-parametric WOTS+C / FORS chain link preimage inversion witness (`dStar < dHonest`). -/
structure CorduroyWotsChainPreimageWith (eng : CorduroyPermEngine) (sk : CorduroySecretKey) where
  adrs                : CorduroyAdrs
  dStar               : Nat
  dHonest             : Nat
  candAtDStar         : Lane4
  preimageLink        : Lane4
  targetLink          : Lane4
  stepStrictlyEarlier : dStar < dHonest
  spongePreimageEq    : corduroySpongeEvalWith eng sk.pkSeed adrs [preimageLink] = targetLink
  honestChainMatch    :
    (∃ layer treeIdx kpIdx chainIdx,
      dHonest ≤ 3 ∧
      adrs = wotsStepAdrs layer treeIdx kpIdx chainIdx (dHonest - 1) ∧
      corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx dStar (dHonest - 1 - dStar) candAtDStar = preimageLink ∧
      preimageLink = corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx 0 (dHonest - 1)
        (corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx) ∧
      targetLink = corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx 0 dHonest
        (corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx)) ∨
    (∃ leafGlobalIdx treeJ leafIdx,
      dStar = 0 ∧ dHonest = 1 ∧
      adrs = forsLeafAdrs leafGlobalIdx treeJ leafIdx ∧
      candAtDStar = preimageLink ∧
      preimageLink = corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx ∧
      targetLink = corduroyHonestForsLeafWith eng sk leafGlobalIdx treeJ leafIdx)

/-- **`Corduroy` Chain Preimage Inversion Witness (`CorduroyWotsChainPreimage`)**:
    Explicit chain link inversion `dStar < dHonest` where `preimageLink` (computed constructively
    from the adversary's forged signature link `candAtDStar`) satisfies
    `corduroySpongeEval sk.pkSeed adrs [preimageLink] = targetLink` against an unrevealed link `< dHonest`. -/
structure CorduroyWotsChainPreimage (sk : CorduroySecretKey) where
  adrs                : CorduroyAdrs
  dStar               : Nat
  dHonest             : Nat
  candAtDStar         : Lane4
  preimageLink        : Lane4
  targetLink          : Lane4
  stepStrictlyEarlier : dStar < dHonest
  spongePreimageEq    : corduroySpongeEval sk.pkSeed adrs [preimageLink] = targetLink
  honestChainMatch    :
    (∃ layer treeIdx kpIdx chainIdx,
      dHonest ≤ 3 ∧
      adrs = wotsStepAdrs layer treeIdx kpIdx chainIdx (dHonest - 1) ∧
      corduroyChainIter sk.pkSeed layer treeIdx kpIdx chainIdx dStar (dHonest - 1 - dStar) candAtDStar = preimageLink ∧
      preimageLink = corduroyChainIter sk.pkSeed layer treeIdx kpIdx chainIdx 0 (dHonest - 1)
        (corduroyWotsSecret sk layer treeIdx kpIdx chainIdx) ∧
      targetLink = corduroyChainIter sk.pkSeed layer treeIdx kpIdx chainIdx 0 dHonest
        (corduroyWotsSecret sk layer treeIdx kpIdx chainIdx)) ∨
    (∃ leafGlobalIdx treeJ leafIdx,
      dStar = 0 ∧ dHonest = 1 ∧
      adrs = forsLeafAdrs leafGlobalIdx treeJ leafIdx ∧
      candAtDStar = preimageLink ∧
      preimageLink = corduroyForsSecret sk leafGlobalIdx treeJ leafIdx ∧
      targetLink = corduroyHonestForsLeaf sk leafGlobalIdx treeJ leafIdx)

inductive CorduroyBreakWith (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (pk : CorduroyPublicKey) (sk : CorduroySecretKey) : Type where
  | msgHashCollision    : CorduroyMsgHashCollisionWith eng cfg → CorduroyBreakWith eng cfg pk sk
  | spongeTweakCollision : CorduroySpongeTweakCollisionWith eng pk.pkSeed → CorduroyBreakWith eng cfg pk sk
  | wotsChainPreimage   : CorduroyWotsChainPreimageWith eng sk → CorduroyBreakWith eng cfg pk sk

/-- **Constructive 3-Way `Corduroy` Security Break Sum (`CorduroyBreak : Type`)**:
    Lives in `Type` (`0 Classical.choice`) and constructively identifies an explicit
    `msgHashCollision`, `spongeTweakCollision`, or `wotsChainPreimage` witness. -/
inductive CorduroyBreak (cfg : CorduroyParams) (pk : CorduroyPublicKey) (sk : CorduroySecretKey) : Type where
  | msgHashCollision    : CorduroyMsgHashCollision cfg → CorduroyBreak cfg pk sk
  | spongeTweakCollision : CorduroySpongeTweakCollision pk.pkSeed → CorduroyBreak cfg pk sk
  | wotsChainPreimage   : CorduroyWotsChainPreimage sk → CorduroyBreak cfg pk sk

/-- Explicit `PSum` view of `CorduroyBreak` (`PSum` of the three concrete `Poseidon2`/sponge problems). -/
def CorduroyBreak.toPSum {cfg : CorduroyParams} {pk : CorduroyPublicKey} {sk : CorduroySecretKey} :
    CorduroyBreak cfg pk sk →
      PSum (CorduroyMsgHashCollision cfg)
        (PSum (CorduroySpongeTweakCollision pk.pkSeed) (CorduroyWotsChainPreimage sk))
  | .msgHashCollision w    => .inl w
  | .spongeTweakCollision w => .inr (.inl w)
  | .wotsChainPreimage w   => .inr (.inr w)

private def CorduroyBreakWith.toCanonical {cfg : CorduroyParams} {pk : CorduroyPublicKey} {sk : CorduroySecretKey} :
    CorduroyBreakWith corduroyPoseidon2Engine cfg pk sk → CorduroyBreak cfg pk sk
  | .msgHashCollision w =>
    .msgHashCollision
      { r1 := w.r1, pk1 := w.pk1, msg1 := w.msg1
        r2 := w.r2, pk2 := w.pk2, msg2 := w.msg2
        distinctInputs := w.distinctInputs
        sameLeafIdx := w.sameLeafIdx
        sameMsgDigest := w.sameMsgDigest }
  | .spongeTweakCollision w =>
    .spongeTweakCollision
      { adrs1 := w.adrs1, in1 := w.in1
        adrs2 := w.adrs2, in2 := w.in2
        distinctTweakOrInput := w.distinctTweakOrInput
        sameSpongeOutput := w.sameSpongeOutput }
  | .wotsChainPreimage w =>
    .wotsChainPreimage
      { adrs := w.adrs, dStar := w.dStar, dHonest := w.dHonest
        candAtDStar := w.candAtDStar, preimageLink := w.preimageLink, targetLink := w.targetLink
        stepStrictlyEarlier := w.stepStrictlyEarlier
        spongePreimageEq := w.spongePreimageEq
        honestChainMatch := w.honestChainMatch }

/-- Oracle signing query record `(msg, rand, sig)` in the `q_sig`-query EUF-CMA game. -/
structure CorduroySignedQuery where
  msg  : Lane4
  rand : CorduroySignRand
  sig  : CorduroySig
  deriving DecidableEq, Repr

/-- Honesty invariant of the `q_sig` signing oracle transcript:
    1. Every query signature `q.sig` was generated by `corduroySign` under a valid counter grind;
    2. Deterministic layer counter search (`tsw_baggy.rs:413-418`): any two queries visiting the
       same static subtree keypair `(L, remL)` grind the identical deterministic counter `layerCtrs[L]`. -/
def CorduroyQuerySetHonestWith (eng : CorduroyPermEngine) (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (queries : List CorduroySignedQuery) : Prop :=
  let pk := corduroyDerivePkWith eng cfg sk
  (∀ q ∈ queries,
    q.sig = corduroySignWith eng cfg sk q.msg q.rand ∧
    CorduroyValidGrindWith eng cfg sk q.msg q.rand) ∧
  (∀ q1 ∈ queries, ∀ q2 ∈ queries, ∀ (L : Nat) (h1 : L < q1.rand.layerCtrs.length) (h2 : L < q2.rand.layerCtrs.length),
    (corduroyHashMsgWith eng cfg q1.sig.rRand pk q1.msg).1 / (2 ^ (L * cfg.subtreeHeight)) =
      (corduroyHashMsgWith eng cfg q2.sig.rRand pk q2.msg).1 / (2 ^ (L * cfg.subtreeHeight)) →
    q1.rand.layerCtrs[L]'h1 = q2.rand.layerCtrs[L]'h2)

def CorduroyQuerySetHonest (cfg : CorduroyParams) (sk : CorduroySecretKey)
    (queries : List CorduroySignedQuery) : Prop :=
  CorduroyQuerySetHonestWith corduroyPoseidon2Engine cfg sk queries

/-- Multi-target FORS subset non-covering predicate at `leafGlobalIdx`:
    either some query already collided with `(leafGlobalIdx, forsIndices)` on `H_msg`, OR there exists
    a FORS tree `j < forsIndices.length` whose selected leaf `forsIndices[j]` was not opened by any
    query hitting `leafGlobalIdx` (holds unconditionally whenever `≤ 1` query hits `leafGlobalIdx`!). -/
def CorduroyForsUncoveredOrCollidingWith (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (pk : CorduroyPublicKey) (queries : List CorduroySignedQuery)
    (leafGlobalIdx : Nat) (forsIndices : List Nat) : Prop :=
  (∃ q ∈ queries,
    (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 = leafGlobalIdx ∧
    (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).2.1 = forsIndices) ∨
  (∃ k, k < forsIndices.length ∧
    ∀ q ∈ queries,
      (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 = leafGlobalIdx →
      (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).2.1.getD k 0 ≠ forsIndices.getD k 0)

def CorduroyForsUncoveredOrColliding (cfg : CorduroyParams) (pk : CorduroyPublicKey)
    (queries : List CorduroySignedQuery) (leafGlobalIdx : Nat) (forsIndices : List Nat) : Prop :=
  CorduroyForsUncoveredOrCollidingWith corduroyPoseidon2Engine cfg pk queries leafGlobalIdx forsIndices

/-- **Unconditional Single-Hit FORS Non-Covering Theorem (`corduroy_single_leaf_hit_uncovered`)**:
    Whenever at most ONE query in `queries` mapped to `leafGlobalIdx`, `CorduroyForsUncoveredOrColliding`
    holds **unconditionally** (zero subset-covering failure probability!). -/
theorem corduroy_single_leaf_hit_uncovered_with (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (pk : CorduroyPublicKey) (queries : List CorduroySignedQuery)
    (leafGlobalIdx : Nat) (forsIndices : List Nat)
    (hForsPos : 0 < cfg.forsTrees) (hForsLen : forsIndices.length = cfg.forsTrees)
    (hAtMostOne : (queries.filter (fun q => (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 == leafGlobalIdx)).length ≤ 1) :
    CorduroyForsUncoveredOrCollidingWith eng cfg pk queries leafGlobalIdx forsIndices := by
  let hits := queries.filter (fun q => (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 == leafGlobalIdx)
  have hMemHits : ∀ q ∈ queries, (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 = leafGlobalIdx → q ∈ hits := by
    intro q hMem hEq
    exact List.mem_filter.mpr ⟨hMem, beq_iff_eq.mpr hEq⟩
  cases hHitsEq : hits with
  | nil =>
    right
    refine ⟨0, by omega, ?_⟩
    intro q hMem hLeaf
    have hIn := hMemHits q hMem hLeaf
    rw [hHitsEq] at hIn
    exact False.elim (List.not_mem_nil hIn)
  | cons q0 restHits =>
    cases restHits with
    | cons _ _ =>
      exfalso
      change hits.length ≤ 1 at hAtMostOne
      rw [hHitsEq] at hAtMostOne
      simp only [List.length_cons] at hAtMostOne
      omega
    | nil =>
      have hq0Mem : q0 ∈ queries ∧ (corduroyHashMsgWith eng cfg q0.sig.rRand pk q0.msg).1 = leafGlobalIdx := by
        have hIn : q0 ∈ hits := by rw [hHitsEq]; exact List.mem_cons_self ..
        obtain ⟨hm, hb⟩ := List.mem_filter.mp hIn
        exact ⟨hm, beq_iff_eq.mp hb⟩
      let qIdxs := (corduroyHashMsgWith eng cfg q0.sig.rRand pk q0.msg).2.1
      by_cases hSameIdxs : qIdxs = forsIndices
      · left
        exact ⟨q0, hq0Mem.1, hq0Mem.2, hSameIdxs⟩
      · right
        have hqLen : qIdxs.length = forsIndices.length :=
          (corduroyHashMsgWith_bounds eng cfg q0.sig.rRand pk q0.msg).2.1.trans hForsLen.symm
        obtain ⟨idx, h1, h2, hDiff⟩ := findListDiffCoord qIdxs forsIndices hqLen hSameIdxs
        refine ⟨idx, h2, ?_⟩
        intro q hMem hLeaf
        have hIn := hMemHits q hMem hLeaf
        rw [hHitsEq, List.mem_singleton] at hIn
        subst hIn
        have hgd1 : qIdxs.getD idx 0 = qIdxs[idx]'h1 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
        have hgd2 : forsIndices.getD idx 0 = forsIndices[idx]'h2 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
        change qIdxs.getD idx 0 ≠ forsIndices.getD idx 0
        rw [hgd1, hgd2]
        exact hDiff

private def extractForwardChainCollisionWith (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (layer treeIdx kpIdx chainIdx : Nat) (steps startStep : Nat) (u1 u2 : Lane4)
    (hNe : u1 ≠ u2)
    (hEq : corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx startStep steps u1 =
      corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx startStep steps u2) :
    CorduroySpongeTweakCollisionWith eng pkSeed :=
  match steps with
  | 0 => False.elim (hNe hEq)
  | steps' + 1 =>
    let v1 := corduroyWotsStepWith eng pkSeed layer treeIdx kpIdx chainIdx startStep u1
    let v2 := corduroyWotsStepWith eng pkSeed layer treeIdx kpIdx chainIdx startStep u2
    if hv : v1 = v2 then
      { adrs1 := wotsStepAdrs layer treeIdx kpIdx chainIdx startStep
        in1   := [u1]
        adrs2 := wotsStepAdrs layer treeIdx kpIdx chainIdx startStep
        in2   := [u2]
        distinctTweakOrInput := fun hPair => by
          injection hPair with _ hIn
          injection hIn with hU _
          exact hNe hU
        sameSpongeOutput := by
          rw [← corduroyWotsStepWith_eq, ← corduroyWotsStepWith_eq]
          exact hv }
    else
      extractForwardChainCollisionWith eng pkSeed layer treeIdx kpIdx chainIdx steps' (startStep + 1) v1 v2 hv hEq
termination_by structural steps

private theorem chainIterWith_one (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (layer treeIdx kpIdx chainIdx startStep : Nat) (val : Lane4) :
    corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx startStep 1 val =
      corduroyWotsStepWith eng pkSeed layer treeIdx kpIdx chainIdx startStep val := rfl

private def extractEarlierDigitBreakWith (eng : CorduroyPermEngine) (sk : CorduroySecretKey)
    (pkSeed : Lane4) (hSeed : pkSeed = sk.pkSeed)
    (layer treeIdx kpIdx chainIdx dStar dHonest : Nat) (chStar : Lane4)
    (hdLt : dStar < dHonest) (hdHonLe : dHonest ≤ 3)
    (hPeakEq : corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx dStar (3 - dStar) chStar =
      corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx 0 3
        (corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx)) :
    PSum (CorduroySpongeTweakCollisionWith eng pkSeed) (CorduroyWotsChainPreimageWith eng sk) :=
  let sec := corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx
  let advPre := corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx dStar (dHonest - 1 - dStar) chStar
  let honPre := corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx 0 (dHonest - 1) sec
  let advAtHon := corduroyWotsStepWith eng sk.pkSeed layer treeIdx kpIdx chainIdx (dHonest - 1) advPre
  let honAtHon := corduroyWotsStepWith eng sk.pkSeed layer treeIdx kpIdx chainIdx (dHonest - 1) honPre
  have hPeakSk : corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx dStar (3 - dStar) chStar =
      corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx 0 3 sec := by
    dsimp only [sec]
    rw [hSeed] at hPeakEq
    exact hPeakEq
  have hAdv1 : advAtHon = corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx dStar (dHonest - dStar) chStar := by
    have hAdd := corduroyChainIterWith_add eng sk.pkSeed layer treeIdx kpIdx chainIdx (dHonest - 1 - dStar) 1 dStar chStar
    rw [show dStar + (dHonest - 1 - dStar) = dHonest - 1 by omega,
        show (dHonest - 1 - dStar) + 1 = dHonest - dStar by omega,
        chainIterWith_one] at hAdd
    exact hAdd
  have hAdv2 : corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx dHonest (3 - dHonest) advAtHon =
      corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx dStar (3 - dStar) chStar := by
    have hAdd := corduroyChainIterWith_add eng sk.pkSeed layer treeIdx kpIdx chainIdx (dHonest - dStar) (3 - dHonest) dStar chStar
    rw [show dStar + (dHonest - dStar) = dHonest by omega,
        show (dHonest - dStar) + (3 - dHonest) = 3 - dStar by omega,
        ← hAdv1] at hAdd
    exact hAdd
  have hHon1 : honAtHon = corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx 0 dHonest sec := by
    have hAdd := corduroyChainIterWith_add eng sk.pkSeed layer treeIdx kpIdx chainIdx (dHonest - 1) 1 0 sec
    rw [Nat.zero_add, show (dHonest - 1) + 1 = dHonest by omega, chainIterWith_one] at hAdd
    exact hAdd
  have hHon2 : corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx dHonest (3 - dHonest) honAtHon =
      corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx 0 3 sec := by
    have hAdd := corduroyChainIterWith_add eng sk.pkSeed layer treeIdx kpIdx chainIdx dHonest (3 - dHonest) 0 sec
    rw [Nat.zero_add, show dHonest + (3 - dHonest) = 3 by omega, ← hHon1] at hAdd
    exact hAdd
  have hTailEq : corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx dHonest (3 - dHonest) advAtHon =
      corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx dHonest (3 - dHonest) honAtHon := by
    rw [hSeed]
    exact (hAdv2.trans hPeakSk).trans hHon2.symm
  if hAtEq : advAtHon = honAtHon then
    if hPreEq : advPre = honPre then
      .inr
        { adrs := wotsStepAdrs layer treeIdx kpIdx chainIdx (dHonest - 1)
          dStar := dStar
          dHonest := dHonest
          candAtDStar := chStar
          preimageLink := advPre
          targetLink := honAtHon
          stepStrictlyEarlier := hdLt
          spongePreimageEq := by
            rw [← corduroyWotsStepWith_eq]
            exact hAtEq
          honestChainMatch := Or.inl ⟨layer, treeIdx, kpIdx, chainIdx, hdHonLe, rfl, rfl, hPreEq, hHon1⟩ }
    else
      .inl
        { adrs1 := wotsStepAdrs layer treeIdx kpIdx chainIdx (dHonest - 1)
          in1   := [advPre]
          adrs2 := wotsStepAdrs layer treeIdx kpIdx chainIdx (dHonest - 1)
          in2   := [honPre]
          distinctTweakOrInput := fun hPair => by
            injection hPair with _ hIn
            injection hIn with hU _
            exact hPreEq hU
          sameSpongeOutput := by
            rw [hSeed, ← corduroyWotsStepWith_eq, ← corduroyWotsStepWith_eq]
            exact hAtEq }
  else
    .inl (extractForwardChainCollisionWith eng pkSeed layer treeIdx kpIdx chainIdx (3 - dHonest) dHonest advAtHon honAtHon hAtEq hTailEq)

private theorem corduroyRecoverPeaksWith_getD (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (layer treeIdx kpIdx : Nat) (digits : List Nat) (chains : List Lane4) (startC i : Nat)
    (hLen : chains.length = digits.length) (hi : i < digits.length) :
    (corduroyRecoverPeaksWith eng pkSeed layer treeIdx kpIdx startC digits chains).getD i lane4Zero =
      corduroyChainIterWith eng pkSeed layer treeIdx kpIdx (startC + i)
        (digits.getD i 0) (3 - digits.getD i 0) (chains.getD i lane4Zero) := by
  induction digits generalizing startC chains i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | cons d ds ih =>
    cases chains with
    | nil => exact absurd hLen (by simp only [List.length_cons, List.length_nil]; omega)
    | cons ch chs =>
      cases i with
      | zero =>
        simp only [corduroyRecoverPeaksWith, List.getD_cons_zero, Nat.add_zero]
      | succ i' =>
        simp only [corduroyRecoverPeaksWith, List.getD_cons_succ]
        rw [ih chs (startC + 1) i' (Nat.succ.inj hLen) (Nat.lt_of_succ_lt_succ hi)]
        have hAssoc : (startC + 1) + i' = startC + (i' + 1) := by omega
        rw [hAssoc]

private def extractMerkleWalkCollisionWith (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (mkAdrs : Nat → Nat → CorduroyAdrs) (leafFn : Nat → Lane4)
    (path : List Lane4) (lvl idx : Nat) (cur : Lane4)
    (hCurNe : cur ≠ computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn lvl idx)
    (hRootEq : walkCorduroyMerklePathWith eng pkSeed mkAdrs lvl idx cur path =
      computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn (lvl + path.length) (idx / (2 ^ path.length))) :
    CorduroySpongeTweakCollisionWith eng pkSeed :=
  match path with
  | [] =>
    False.elim (hCurNe (by
      dsimp only [walkCorduroyMerklePathWith, List.length_nil] at hRootEq
      rw [Nat.add_zero, Nat.pow_zero, Nat.div_one] at hRootEq
      exact hRootEq))
  | sib :: rest =>
    let parentIdx  := idx / 2
    let leftStar   := if idx % 2 == 0 then cur else sib
    let rightStar  := if idx % 2 == 0 then sib else cur
    let parentStar := corduroyMerkleHashWith eng pkSeed (mkAdrs lvl parentIdx) leftStar rightStar
    let honLeft    := computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn lvl (2 * parentIdx)
    let honRight   := computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn lvl (2 * parentIdx + 1)
    let honParent  := computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn (lvl + 1) parentIdx
    have hWalkStep : walkCorduroyMerklePathWith eng pkSeed mkAdrs lvl idx cur (sib :: rest) =
        walkCorduroyMerklePathWith eng pkSeed mkAdrs (lvl + 1) parentIdx parentStar rest := by
      dsimp only [walkCorduroyMerklePathWith, parentIdx, parentStar, leftStar, rightStar]
      by_cases hEven : (idx % 2 == 0) = true
      · simp only [hEven, ↓reduceIte]
      · have hFalse : (idx % 2 == 0) = false := Bool.eq_false_iff.mpr hEven
        simp only [hFalse, Bool.false_eq_true, ↓reduceIte]
    if hParEq : parentStar = honParent then
      { adrs1 := mkAdrs lvl parentIdx
        in1   := [leftStar, rightStar]
        adrs2 := mkAdrs lvl parentIdx
        in2   := [honLeft, honRight]
        distinctTweakOrInput := fun hPair => by
          injection hPair with _ hIn
          injection hIn with hL hTail
          injection hTail with hR _
          dsimp only [leftStar, rightStar, honLeft, honRight, parentIdx] at hL hR
          rcases Nat.mod_two_eq_zero_or_one idx with hEv | hOd
          · have hIdx : 2 * (idx / 2) = idx := by omega
            simp only [hEv, beq_self_eq_true, ↓reduceIte, hIdx] at hL
            exact hCurNe hL
          · have hNe0 : (idx % 2 == 0) = false := by rw [hOd]; decide
            have hIdx : 2 * (idx / 2) + 1 = idx := by omega
            simp only [hNe0, Bool.false_eq_true, ↓reduceIte, hIdx] at hR
            exact hCurNe hR
        sameSpongeOutput := hParEq }
    else
      extractMerkleWalkCollisionWith eng pkSeed mkAdrs leafFn rest (lvl + 1) parentIdx parentStar hParEq (by
        have hNextRoot : walkCorduroyMerklePathWith eng pkSeed mkAdrs (lvl + 1) parentIdx parentStar rest =
            computeCorduroyMerkleNodeWith eng pkSeed mkAdrs leafFn (lvl + (sib :: rest).length)
              (idx / (2 ^ (sib :: rest).length)) := hWalkStep.symm.trans hRootEq
        have hLvl : lvl + (sib :: rest).length = (lvl + 1) + rest.length := by
          simp only [List.length_cons]; omega
        have hDiv : idx / (2 ^ (sib :: rest).length) = parentIdx / (2 ^ rest.length) := by
          dsimp only [parentIdx]
          simp only [List.length_cons]
          rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ rest.length)]
        rw [hLvl, hDiv] at hNextRoot
        exact hNextRoot)
termination_by structural path

private def findQueryVisitingRemWith (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (pk : CorduroyPublicKey) (L targetRem : Nat) (qs : List CorduroySignedQuery) :
    Option { q : CorduroySignedQuery // q ∈ qs ∧
      (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 / (2 ^ (L * cfg.subtreeHeight)) = targetRem } :=
  match qs with
  | [] => none
  | q :: rest =>
    if hEq : (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 / (2 ^ (L * cfg.subtreeHeight)) = targetRem then
      some ⟨q, ⟨List.mem_cons_self .., hEq⟩⟩
    else
      match findQueryVisitingRemWith eng cfg pk L targetRem rest with
      | none => none
      | some ⟨q', hMem', hEq'⟩ => some ⟨q', ⟨List.mem_cons_of_mem _ hMem', hEq'⟩⟩
termination_by structural qs

private theorem corduroyVerifyLayerWith_inv (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (pk : CorduroyPublicKey) (layer treeIdx kpIdx : Nat) (childRoot nextRoot : Lane4) (lsig : CorduroyLayerSig)
    (hVer : corduroyVerifyLayerWith eng cfg pk layer treeIdx kpIdx childRoot lsig = some nextRoot) :
    lsig.wotsChains.length = cfg.wotsChains ∧
    lsig.authPath.length = cfg.subtreeHeight ∧
    lsig.tswCtr < 2 ^ 56 ∧
    let hmsg := corduroyLayerHmsgWith eng pk layer treeIdx kpIdx lsig.tswCtr childRoot
    let digits := corduroyExtractDigits cfg.wotsChains hmsg
    let peaks := corduroyRecoverPeaksWith eng pk.pkSeed layer treeIdx kpIdx 0 digits lsig.wotsChains
    let wotsPk := corduroyWotsPkCompressWith eng pk.pkSeed layer treeIdx kpIdx peaks
    natListSum digits = cfg.targetSum ∧
    walkCorduroyMerklePathWith eng pk.pkSeed (xmssMerkleAdrs layer treeIdx) 0 kpIdx wotsPk lsig.authPath = nextRoot := by
  unfold corduroyVerifyLayerWith at hVer
  by_cases hGuard : (lsig.wotsChains.length == cfg.wotsChains && lsig.authPath.length == cfg.subtreeHeight &&
      decide (lsig.tswCtr < 2 ^ 56)) = true
  · simp only [hGuard, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hVer
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hGuard
    rcases hGuard with ⟨⟨hChLen, hPathLen⟩, hCtrLt⟩
    refine ⟨hChLen, hPathLen, hCtrLt, ?_⟩
    dsimp only
    let hmsg := corduroyLayerHmsgWith eng pk layer treeIdx kpIdx lsig.tswCtr childRoot
    let digits := corduroyExtractDigits cfg.wotsChains hmsg
    change (if !(natListSum digits == cfg.targetSum) then none else _) = some nextRoot at hVer
    by_cases hSum : (natListSum digits == cfg.targetSum) = true
    · simp only [hSum, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hVer
      exact ⟨beq_iff_eq.mp hSum, hVer⟩
    · have hFalse : (natListSum digits == cfg.targetSum) = false := Bool.eq_false_iff.mpr hSum
      simp only [hFalse, Bool.not_false, ↓reduceIte] at hVer
      exact absurd hVer (by simp)
  · have hFalse : (lsig.wotsChains.length == cfg.wotsChains && lsig.authPath.length == cfg.subtreeHeight &&
        decide (lsig.tswCtr < 2 ^ 56)) = false := Bool.eq_false_iff.mpr hGuard
    simp only [hFalse, Bool.not_false, ↓reduceIte] at hVer
    exact absurd hVer (by simp)

/-- Single-layer WOTS+C + Merkle constructive break extractor when `childRoot ≠ honChildRt` yet
    `corduroyVerifyLayerWith` climbs to the honest subtree root! -/
private def extractLayerBreakWith (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (sk : CorduroySecretKey) (pk : CorduroyPublicKey)
    (hPk : pk = corduroyDerivePkWith eng cfg sk)
    (hWf : cfg.wellFormed = true) (hFullDigits : cfg.wotsChains = 128)
    (queries : List CorduroySignedQuery) (hHonQ : CorduroyQuerySetHonestWith eng cfg sk queries)
    (L remIdx : Nat) (hLLt : L < cfg.numLayers)
    (childRtStar : Lane4) (lsig : CorduroyLayerSig)
    (hChildNe : childRtStar ≠
      (if L = 0 then corduroyHonestForsPkWith eng cfg sk remIdx
       else corduroyHonestSubtreeRootWith eng cfg sk (L - 1) remIdx))
    (hVer : corduroyVerifyLayerWith eng cfg pk L (remIdx / (2 ^ cfg.subtreeHeight))
      (remIdx % (2 ^ cfg.subtreeHeight)) childRtStar lsig =
      some (corduroyHonestSubtreeRootWith eng cfg sk L (remIdx / (2 ^ cfg.subtreeHeight)))) :
    PSum (CorduroySpongeTweakCollisionWith eng pk.pkSeed) (CorduroyWotsChainPreimageWith eng sk) :=
  let subLeaves := 2 ^ cfg.subtreeHeight
  let trL := remIdx / subLeaves
  let kpL := remIdx % subLeaves
  have hSeed : pk.pkSeed = sk.pkSeed := by rw [hPk]; rfl
  have hKpLt : kpL < subLeaves := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hInv := corduroyVerifyLayerWith_inv eng cfg pk L trL kpL childRtStar
    (corduroyHonestSubtreeRootWith eng cfg sk L trL) lsig hVer
  let hmsgStar := corduroyLayerHmsgWith eng pk L trL kpL lsig.tswCtr childRtStar
  let digitsStar := corduroyExtractDigits cfg.wotsChains hmsgStar
  let peaksStar := corduroyRecoverPeaksWith eng pk.pkSeed L trL kpL 0 digitsStar lsig.wotsChains
  let wotsPkStar := corduroyWotsPkCompressWith eng pk.pkSeed L trL kpL peaksStar
  let honPeaks := corduroyHonestWotsPeaksWith eng cfg sk L trL kpL
  let honWotsPk := corduroyHonestWotsPkWith eng cfg sk L trL kpL
  if hWotsNe : wotsPkStar ≠ honWotsPk then
    .inl (extractMerkleWalkCollisionWith eng pk.pkSeed (xmssMerkleAdrs L trL)
      (corduroyHonestWotsPkWith eng cfg sk L trL) lsig.authPath 0 kpL wotsPkStar
      (by
        rw [hSeed]
        exact hWotsNe)
      (by
        have hWalk := hInv.2.2.2.2
        have hPathLen := hInv.2.1
        rw [Nat.zero_add, hPathLen, Nat.div_eq_of_lt hKpLt]
        dsimp only [wotsPkStar, peaksStar, digitsStar, hmsgStar, corduroyHonestSubtreeRootWith] at hWalk ⊢
        rw [hSeed] at hWalk ⊢
        exact hWalk))
  else
    have hWotsEq : wotsPkStar = honWotsPk := Decidable.of_not_not hWotsNe
    if hPeaksNe : peaksStar ≠ honPeaks then
      .inl
        { adrs1 := wotsPkAdrs L trL kpL
          in1   := peaksStar
          adrs2 := wotsPkAdrs L trL kpL
          in2   := honPeaks
          distinctTweakOrInput := fun hPair => by
            injection hPair with _ hIn
            exact hPeaksNe hIn
          sameSpongeOutput := by
            have hComp : corduroyWotsPkCompressWith eng pk.pkSeed L trL kpL peaksStar =
                corduroyWotsPkCompressWith eng pk.pkSeed L trL kpL honPeaks := by
              change wotsPkStar = _
              rw [hWotsEq]
              unfold honWotsPk corduroyHonestWotsPkWith
              rw [hSeed]
            exact hComp }
    else
      have hPeaksEq : peaksStar = honPeaks := Decidable.of_not_not hPeaksNe
      have hTargetLt : cfg.targetSum < 3 * cfg.wotsChains := by
        unfold CorduroyParams.wellFormed at hWf
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
        exact hWf.1.1.1.1.1.1.1.1.2
      have hChainsLe : cfg.wotsChains ≤ 128 := Nat.le_of_eq hFullDigits
      have hDigStarSpec := corduroyExtractDigits_spec hChainsLe hmsgStar
      have hDigLen : digitsStar.length = cfg.wotsChains := hDigStarSpec.1
      match findQueryVisitingRemWith eng cfg pk L remIdx queries with
      | none =>
        let rep3 := List.replicate cfg.wotsChains 3
        have hRepSum : natListSum rep3 = 3 * cfg.wotsChains := natListSum_replicate cfg.wotsChains 3
        have hSumStar : natListSum digitsStar = cfg.targetSum := hInv.2.2.2.1
        have hNeRep : digitsStar ≠ rep3 := fun hEq => by
          rw [hEq, hRepSum] at hSumStar
          omega
        let ⟨c, hc⟩ := findSmallerDigitCoord digitsStar rep3
          (hDigLen.trans List.length_replicate.symm) hNeRep (by omega)
        have hcLt : c < cfg.wotsChains := by
          rcases hc with ⟨h1, _, _⟩
          omega
        have hdStarLt3 : digitsStar.getD c 0 < 3 := by
          rcases hc with ⟨h1, h2, hLtRep⟩
          have hgd1 : digitsStar.getD c 0 = digitsStar[c]'h1 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
          have hgd2 : rep3[c]'h2 = 3 := List.getElem_replicate h2
          rw [hgd2] at hLtRep
          rw [hgd1]
          exact hLtRep
        have hCoordPeak : corduroyChainIterWith eng pk.pkSeed L trL kpL c
            (digitsStar.getD c 0) (3 - digitsStar.getD c 0) (lsig.wotsChains.getD c lane4Zero) =
            corduroyChainIterWith eng sk.pkSeed L trL kpL c 0 3 (corduroyWotsSecretWith eng sk L trL kpL c) := by
          have hGet := congrArg (fun xs => xs.getD c lane4Zero) hPeaksEq
          dsimp only [peaksStar, honPeaks, corduroyHonestWotsPeaksWith] at hGet
          rw [corduroyRecoverPeaksWith_getD eng pk.pkSeed L trL kpL digitsStar lsig.wotsChains 0 c
                (hInv.1.trans hDigLen.symm) (by rw [hDigLen]; exact hcLt),
              Nat.zero_add,
              getD_map_range _ lane4Zero cfg.wotsChains c hcLt] at hGet
          exact hGet
        extractEarlierDigitBreakWith eng sk pk.pkSeed hSeed L trL kpL c
          (digitsStar.getD c 0) 3 (lsig.wotsChains.getD c lane4Zero) hdStarLt3 (Nat.le_refl 3) hCoordPeak
      | some ⟨q, hqMem, hqRemEq⟩ =>
        have hqHon := hHonQ.1 q hqMem
        have hqCtrsLen : q.rand.layerCtrs.length = cfg.numLayers := hqHon.2.2.1
        have hLLtQ : L < q.rand.layerCtrs.length := by omega
        let ctrHon := q.rand.layerCtrs[L]'hLLtQ
        let honChildRt :=
          if L = 0 then corduroyHonestForsPkWith eng cfg sk remIdx
          else corduroyHonestSubtreeRootWith eng cfg sk (L - 1) remIdx
        let hmsgHon := corduroyLayerHmsgWith eng pk L trL kpL ctrHon honChildRt
        let digitsHon := corduroyExtractDigits cfg.wotsChains hmsgHon
        have hDigHonSpec := corduroyExtractDigits_spec hChainsLe hmsgHon
        have hSumHon : natListSum digitsHon = cfg.targetSum := by
          have hGrindL := hqHon.2.2.2 L hLLtQ
          dsimp only at hGrindL
          have hSigRand : q.sig.rRand = corduroyPrfMsgWith eng sk q.rand.optRand q.msg := by
            rw [hqHon.1]; rfl
          have hRemMatch : (corduroyHashMsgWith eng cfg (corduroyPrfMsgWith eng sk q.rand.optRand q.msg)
              (corduroyDerivePkWith eng cfg sk) q.msg).1 / (2 ^ (L * cfg.subtreeHeight)) = remIdx := by
            rw [← hSigRand, ← hPk]
            exact hqRemEq
          have hChildMatch :
              (if L = 0 then
                corduroyHonestForsPkWith eng cfg sk
                  (corduroyHashMsgWith eng cfg (corduroyPrfMsgWith eng sk q.rand.optRand q.msg)
                    (corduroyDerivePkWith eng cfg sk) q.msg).1
               else
                corduroyHonestSubtreeRootWith eng cfg sk (L - 1)
                  ((corduroyHashMsgWith eng cfg (corduroyPrfMsgWith eng sk q.rand.optRand q.msg)
                    (corduroyDerivePkWith eng cfg sk) q.msg).1 / (2 ^ (L * cfg.subtreeHeight)))) = honChildRt := by
            dsimp only [honChildRt]
            by_cases hL0 : L = 0
            · subst hL0
              simp only [↓reduceIte, Nat.zero_mul, Nat.pow_zero, Nat.div_one] at hRemMatch ⊢
              rw [hRemMatch]
            · simp only [hL0, ↓reduceIte]
              rw [hRemMatch]
          have hSumRaw := hGrindL.2
          rw [hChildMatch, hRemMatch, ← hPk] at hSumRaw
          exact hSumRaw
        if hDigEq : digitsStar = digitsHon then
          have hHmsgEq : hmsgStar = hmsgHon := by
            dsimp only [digitsStar, digitsHon] at hDigEq
            rw [hFullDigits] at hDigEq
            exact corduroyExtractDigits_128_injective hDigEq
          .inl
            { adrs1 := layerHmsgAdrs L trL kpL lsig.tswCtr
              in1   := [pk.pkRoot, childRtStar]
              adrs2 := layerHmsgAdrs L trL kpL ctrHon
              in2   := [pk.pkRoot, honChildRt]
              distinctTweakOrInput := fun hPair => by
                injection hPair with _ hIn
                injection hIn with _ hTail
                injection hTail with hChildEq _
                exact hChildNe hChildEq
              sameSpongeOutput := hHmsgEq }
        else
          let ⟨c, hc⟩ := wotsTargetSum_reused_smaller_digit cfg.targetSum digitsStar digitsHon
            (hDigLen.trans hDigHonSpec.1.symm) hDigEq hInv.2.2.2.1 hSumHon
          have hcLt : c < cfg.wotsChains := by
            rcases hc with ⟨h1, _, _⟩
            omega
          have hdLt : digitsStar.getD c 0 < digitsHon.getD c 0 := by
            rcases hc with ⟨h1, h2, hLt⟩
            have hgd1 : digitsStar.getD c 0 = digitsStar[c]'h1 := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
            have hgd2 : digitsHon.getD c 0 = digitsHon[c]'h2 := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
            rw [hgd1, hgd2]
            exact hLt
          have hdHonLe3 : digitsHon.getD c 0 ≤ 3 := by
            rcases hc with ⟨_, h2, _⟩
            have hgd2 : digitsHon.getD c 0 = digitsHon[c]'h2 := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
            have hLt4 := hDigHonSpec.2 (digitsHon[c]'h2) (List.getElem_mem h2)
            rw [hgd2]
            omega
          have hCoordPeak : corduroyChainIterWith eng pk.pkSeed L trL kpL c
              (digitsStar.getD c 0) (3 - digitsStar.getD c 0) (lsig.wotsChains.getD c lane4Zero) =
              corduroyChainIterWith eng sk.pkSeed L trL kpL c 0 3 (corduroyWotsSecretWith eng sk L trL kpL c) := by
            have hGet := congrArg (fun xs => xs.getD c lane4Zero) hPeaksEq
            dsimp only [peaksStar, honPeaks, corduroyHonestWotsPeaksWith] at hGet
            rw [corduroyRecoverPeaksWith_getD eng pk.pkSeed L trL kpL digitsStar lsig.wotsChains 0 c
                  (hInv.1.trans hDigLen.symm) (by rw [hDigLen]; exact hcLt),
                Nat.zero_add,
                getD_map_range _ lane4Zero cfg.wotsChains c hcLt] at hGet
            exact hGet
          extractEarlierDigitBreakWith eng sk pk.pkSeed hSeed L trL kpL c
            (digitsStar.getD c 0) (digitsHon.getD c 0) (lsig.wotsChains.getD c lane4Zero)
            hdLt hdHonLe3 hCoordPeak

/-- Walk `lsigs` from a forged child root `curRoot ≠ honestChildRt` to `topRoot = honestTopRoot`,
    constructively extracting the break at the exact layer where the forged path merges into the honest hypertree. -/
private def extractHypertreeDivergenceWith (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (sk : CorduroySecretKey) (pk : CorduroyPublicKey)
    (hPk : pk = corduroyDerivePkWith eng cfg sk)
    (hWf : cfg.wellFormed = true) (hFullDigits : cfg.wotsChains = 128)
    (queries : List CorduroySignedQuery) (hHonQ : CorduroyQuerySetHonestWith eng cfg sk queries)
    (lsigs : List CorduroyLayerSig) (startL remIdx : Nat) (curRoot : Lane4)
    (hPos : 0 < lsigs.length)
    (hSumL : startL + lsigs.length = cfg.numLayers)
    (hRemLt : remIdx < 2 ^ (lsigs.length * cfg.subtreeHeight))
    (hCurNe : curRoot ≠ (if startL = 0 then corduroyHonestForsPkWith eng cfg sk remIdx
                         else corduroyHonestSubtreeRootWith eng cfg sk (startL - 1) remIdx))
    (hHypVer : corduroyVerifyHypertreeWith eng cfg pk startL remIdx curRoot lsigs =
      some (corduroyHonestSubtreeRootWith eng cfg sk (cfg.numLayers - 1) 0)) :
    PSum (CorduroySpongeTweakCollisionWith eng pk.pkSeed) (CorduroyWotsChainPreimageWith eng sk) :=
  match lsigs with
  | [] => False.elim (Nat.not_lt_zero 0 hPos)
  | lsig :: rest =>
    let subLeaves := 2 ^ cfg.subtreeHeight
    let trL := remIdx / subLeaves
    match hLayer : corduroyVerifyLayerWith eng cfg pk startL trL (remIdx % subLeaves) curRoot lsig with
    | none =>
      False.elim (by
        dsimp only [corduroyVerifyHypertreeWith] at hHypVer
        change (match corduroyVerifyLayerWith eng cfg pk startL trL (remIdx % subLeaves) curRoot lsig with
                | none => none
                | some nextRoot => corduroyVerifyHypertreeWith eng cfg pk (startL + 1) trL nextRoot rest) = _ at hHypVer
        simp [hLayer] at hHypVer)
    | some nextRoot =>
      have hRestVer : corduroyVerifyHypertreeWith eng cfg pk (startL + 1) trL nextRoot rest =
          some (corduroyHonestSubtreeRootWith eng cfg sk (cfg.numLayers - 1) 0) := by
        dsimp only [corduroyVerifyHypertreeWith] at hHypVer
        change (match corduroyVerifyLayerWith eng cfg pk startL trL (remIdx % subLeaves) curRoot lsig with
                | none => none
                | some nextRoot => corduroyVerifyHypertreeWith eng cfg pk (startL + 1) trL nextRoot rest) = _ at hHypVer
        rw [hLayer] at hHypVer
        exact hHypVer
      if hMerge : nextRoot = corduroyHonestSubtreeRootWith eng cfg sk startL trL then
        extractLayerBreakWith eng cfg sk pk hPk hWf hFullDigits queries hHonQ startL remIdx
          (by simp only [List.length_cons] at hSumL; omega) curRoot lsig hCurNe
          (by rw [hLayer, hMerge])
      else
        match rest with
        | [] =>
          False.elim (by
            dsimp only [corduroyVerifyHypertreeWith] at hRestVer
            injection hRestVer with hTopEq
            simp only [List.length_singleton] at hSumL hRemLt
            rw [Nat.one_mul] at hRemLt
            have hTr0 : trL = 0 := Nat.div_eq_of_lt hRemLt
            have hLTop : startL = cfg.numLayers - 1 := by omega
            rw [← hLTop, ← hTr0] at hTopEq
            exact hMerge hTopEq)
        | lsig1 :: tail =>
          extractHypertreeDivergenceWith eng cfg sk pk hPk hWf hFullDigits queries hHonQ
            (lsig1 :: tail) (startL + 1) trL nextRoot
            (Nat.zero_lt_succ _)
            (by simp only [List.length_cons] at hSumL ⊢; omega)
            (by
              dsimp only [trL, subLeaves]
              simp only [List.length_cons] at hRemLt ⊢
              have hPow : 2 ^ ((tail.length + 1 + 1) * cfg.subtreeHeight) =
                  (2 ^ cfg.subtreeHeight) * (2 ^ ((tail.length + 1) * cfg.subtreeHeight)) := by
                rw [← Nat.pow_add]
                have hE : (tail.length + 1 + 1) * cfg.subtreeHeight =
                    cfg.subtreeHeight + (tail.length + 1) * cfg.subtreeHeight := by
                  rw [Nat.add_mul (tail.length + 1) 1 cfg.subtreeHeight, Nat.one_mul, Nat.add_comm]
                rw [hE]
              rw [hPow] at hRemLt
              apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos cfg.subtreeHeight)).mpr
              simpa only [Nat.mul_comm] using hRemLt)
            (by
              simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
              exact hMerge)
            hRestVer
termination_by structural lsigs

/-- Extract either a FORS sponge/Merkle collision OR exact secret recovery across all `k` FORS trees. -/
private def extractForsTreesCollisionOrSecretsWith (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (sk : CorduroySecretKey) (pkSeed : Lane4) (hSeed : pkSeed = sk.pkSeed) (leafGlobalIdx : Nat)
    (idxs : List Nat) (ops : List CorduroyForsOpening) (roots : List Lane4) (startJ : Nat)
    (hVer : corduroyVerifyForsTreesWith eng cfg pkSeed leafGlobalIdx startJ idxs ops = some roots)
    (hRootsEq : roots = ((List.range idxs.length).map fun t => corduroyHonestForsTreeRootWith eng cfg sk leafGlobalIdx (startJ + t))) :
    PSum (CorduroySpongeTweakCollisionWith eng pkSeed)
      (∀ (t : Nat), t < idxs.length →
        (ops.getD t { secretVal := lane4Zero, authPath := [] }).secretVal =
          corduroyForsSecretWith eng sk leafGlobalIdx (startJ + t) (idxs.getD t 0)) :=
  match idxs, ops with
  | [], [] => .inr (fun t ht => False.elim (Nat.not_lt_zero t ht))
  | [], _ :: _ => False.elim (by simp [corduroyVerifyForsTreesWith] at hVer)
  | _ :: _, [] => False.elim (by simp [corduroyVerifyForsTreesWith] at hVer)
  | idx :: restIdxs, op :: restOps =>
    have hUnpack : idx < 2 ^ cfg.forsHeight ∧ op.authPath.length = cfg.forsHeight ∧
        ∃ restRts, corduroyVerifyForsTreesWith eng cfg pkSeed leafGlobalIdx (startJ + 1) restIdxs restOps = some restRts ∧
          roots = walkCorduroyMerklePathWith eng pkSeed (forsNodeAdrs leafGlobalIdx startJ) 0 idx
            (corduroyForsLeafHashWith eng pkSeed leafGlobalIdx startJ idx op.secretVal) op.authPath :: restRts := by
      dsimp only [corduroyVerifyForsTreesWith] at hVer
      by_cases hG : (decide (idx < 2 ^ cfg.forsHeight) && (op.authPath.length == cfg.forsHeight)) = true
      · simp only [hG, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hVer
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hG
        refine ⟨hG.1, hG.2, ?_⟩
        cases hRec : corduroyVerifyForsTreesWith eng cfg pkSeed leafGlobalIdx (startJ + 1) restIdxs restOps with
        | none => rw [hRec] at hVer; exact absurd hVer (by simp)
        | some restRts =>
          rw [hRec] at hVer
          injection hVer with hEqR
          exact ⟨restRts, rfl, hEqR.symm⟩
      · have hFalse : (decide (idx < 2 ^ cfg.forsHeight) && (op.authPath.length == cfg.forsHeight)) = false :=
          Bool.eq_false_iff.mpr hG
        simp only [hFalse, Bool.not_false, ↓reduceIte] at hVer
        exact absurd hVer (by simp)
    let leaf0 := corduroyForsLeafHashWith eng pkSeed leafGlobalIdx startJ idx op.secretVal
    let honLeaf0 := corduroyHonestForsLeafWith eng sk leafGlobalIdx startJ idx
    if hLeafNe : leaf0 ≠ honLeaf0 then
      .inl (extractMerkleWalkCollisionWith eng pkSeed (forsNodeAdrs leafGlobalIdx startJ)
        (corduroyHonestForsLeafWith eng sk leafGlobalIdx startJ) op.authPath 0 idx leaf0
        (by
          rw [hSeed]
          exact hLeafNe)
        (by
          obtain ⟨hIdxLt, hPathLen, restRts, _, hRtsCons⟩ := hUnpack
          rw [hRtsCons] at hRootsEq
          simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.cons.injEq] at hRootsEq
          have hRt0 := hRootsEq.1
          rw [Nat.zero_add, hPathLen, Nat.div_eq_of_lt hIdxLt]
          dsimp only [leaf0, corduroyHonestForsTreeRootWith] at hRt0 ⊢
          rw [hSeed] at hRt0 ⊢
          exact hRt0))
    else
      have hLeafEq : leaf0 = honLeaf0 := Decidable.of_not_not hLeafNe
      if hSecNe : op.secretVal ≠ corduroyForsSecretWith eng sk leafGlobalIdx startJ idx then
        .inl
          { adrs1 := forsLeafAdrs leafGlobalIdx startJ idx
            in1   := [op.secretVal]
            adrs2 := forsLeafAdrs leafGlobalIdx startJ idx
            in2   := [corduroyForsSecretWith eng sk leafGlobalIdx startJ idx]
            distinctTweakOrInput := fun hPair => by
              injection hPair with _ hIn
              injection hIn with hU _
              exact hSecNe hU
            sameSpongeOutput := by
              dsimp only [leaf0, honLeaf0, corduroyForsLeafHashWith, corduroyHonestForsLeafWith] at hLeafEq
              rw [hSeed] at hLeafEq ⊢
              exact hLeafEq }
      else
        have hSecEq : op.secretVal = corduroyForsSecretWith eng sk leafGlobalIdx startJ idx :=
          Decidable.of_not_not hSecNe
        let restRts := (List.range restIdxs.length).map fun t =>
          corduroyHonestForsTreeRootWith eng cfg sk leafGlobalIdx ((startJ + 1) + t)
        have hRestVer : corduroyVerifyForsTreesWith eng cfg pkSeed leafGlobalIdx (startJ + 1) restIdxs restOps =
            some restRts := by
          obtain ⟨_, _, rts', hRec, hRtsCons⟩ := hUnpack
          rw [hRtsCons] at hRootsEq
          simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.cons.injEq] at hRootsEq
          have hTailEq : rts' = restRts := by
            rw [hRootsEq.2, List.map_map]
            apply List.map_congr_left
            intro t _
            dsimp only [Function.comp]
            have hAssoc : startJ + (t + 1) = (startJ + 1) + t := by omega
            rw [hAssoc]
          rw [← hTailEq]
          exact hRec
        match extractForsTreesCollisionOrSecretsWith eng cfg sk pkSeed hSeed leafGlobalIdx
                restIdxs restOps restRts (startJ + 1) hRestVer rfl with
        | .inl col => .inl col
        | .inr hTailSec =>
          .inr (fun t ht => by
            cases t with
            | zero =>
              simp only [List.getD_cons_zero, Nat.add_zero]
              exact hSecEq
            | succ t' =>
              simp only [List.getD_cons_succ]
              have ht' : t' < restIdxs.length := Nat.lt_of_succ_lt_succ ht
              have hStep := hTailSec t' ht'
              have hAssoc : (startJ + 1) + t' = startJ + (t' + 1) := by omega
              rw [hAssoc] at hStep
              exact hStep)
termination_by structural idxs

private def findCollidingMsgHashQueryWith (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (pk : CorduroyPublicKey) (leafGlobalIdx : Nat) (forsIndices : List Nat)
    (qs : List CorduroySignedQuery) :
    Option { q : CorduroySignedQuery // q ∈ qs ∧
      (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 = leafGlobalIdx ∧
      (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).2.1 = forsIndices } :=
  match qs with
  | [] => none
  | q :: rest =>
    if hMatch : (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 = leafGlobalIdx ∧
                (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).2.1 = forsIndices then
      some ⟨q, ⟨List.mem_cons_self .., hMatch⟩⟩
    else
      match findCollidingMsgHashQueryWith eng cfg pk leafGlobalIdx forsIndices rest with
      | none => none
      | some ⟨q', hMem', hM'⟩ => some ⟨q', ⟨List.mem_cons_of_mem _ hMem', hM'⟩⟩
termination_by structural qs

private theorem findCollidingMsgHashQueryWith_none (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (pk : CorduroyPublicKey) (leafGlobalIdx : Nat) (forsIndices : List Nat)
    (qs : List CorduroySignedQuery)
    (hNone : findCollidingMsgHashQueryWith eng cfg pk leafGlobalIdx forsIndices qs = none) :
    ∀ q ∈ qs, ¬((corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 = leafGlobalIdx ∧
                (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).2.1 = forsIndices) := by
  induction qs with
  | nil => intro _ hMem; exact False.elim (List.not_mem_nil hMem)
  | cons q rest ih =>
    simp only [findCollidingMsgHashQueryWith] at hNone
    by_cases hM : (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 = leafGlobalIdx ∧
                  (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).2.1 = forsIndices
    · simp only [hM] at hNone
      exact absurd hNone (by simp)
    · simp only [hM] at hNone
      have hSubNone : findCollidingMsgHashQueryWith eng cfg pk leafGlobalIdx forsIndices rest = none := by
        cases hSub : findCollidingMsgHashQueryWith eng cfg pk leafGlobalIdx forsIndices rest with
        | none => rfl
        | some p => rw [hSub] at hNone; exact absurd hNone (by simp)
      intro q' hMem'
      rcases List.mem_cons.mp hMem' with rfl | hTail
      · exact hM
      · exact ih hSubNone q' hTail

/-- Engine-parametric constructive multi-target EUF-CMA witness extractor. -/
private def corduroy_euf_cma_extract_with
    (eng : CorduroyPermEngine) (cfg : CorduroyParams)
    (sk : CorduroySecretKey) (pk : CorduroyPublicKey)
    (queries : List CorduroySignedQuery)
    (msgStar : Lane4) (sigStar : CorduroySig)
    (hPk : pk = corduroyDerivePkWith eng cfg sk)
    (hFullDigits : cfg.wotsChains = 128)
    (hHonQ : CorduroyQuerySetHonestWith eng cfg sk queries)
    (hFresh : msgStar ∉ queries.map (·.msg))
    (hVer : corduroyVerifyWith eng cfg pk msgStar sigStar = true)
    (hForsRes : CorduroyForsUncoveredOrCollidingWith eng cfg pk queries
      (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).1
      (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).2.1) :
    CorduroyBreakWith eng cfg pk sk :=
  have hSeed : pk.pkSeed = sk.pkSeed := by rw [hPk]; rfl
  have hUnpackVer : cfg.wellFormed = true ∧ sigStar.layerSigs.length = cfg.numLayers ∧
      ∃ forsPkStar,
        corduroyRecoverForsPkWith eng cfg pk.pkSeed
          (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).1
          (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).2.1
          sigStar.forsOpenings = some forsPkStar ∧
        corduroyVerifyHypertreeWith eng cfg pk 0
          (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).1
          forsPkStar sigStar.layerSigs = some pk.pkRoot := by
    unfold corduroyVerifyWith at hVer
    by_cases hG : (cfg.wellFormed && (sigStar.layerSigs.length == cfg.numLayers)) = true
    · simp only [hG, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hVer
      simp only [Bool.and_eq_true, beq_iff_eq] at hG
      refine ⟨hG.1, hG.2, ?_⟩
      cases hF : corduroyRecoverForsPkWith eng cfg pk.pkSeed
          (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).1
          (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).2.1
          sigStar.forsOpenings with
      | none => rw [hF] at hVer; exact absurd hVer (by simp)
      | some forsPkStar =>
        rw [hF] at hVer
        dsimp only at hVer
        cases hH : corduroyVerifyHypertreeWith eng cfg pk 0
            (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).1
            forsPkStar sigStar.layerSigs with
        | none => rw [hH] at hVer; exact absurd hVer (by simp)
        | some topRt =>
          rw [hH] at hVer
          dsimp only at hVer
          rw [beq_iff_eq] at hVer
          rw [hVer] at hH
          exact ⟨forsPkStar, rfl, hH⟩
    · have hFalse : (cfg.wellFormed && (sigStar.layerSigs.length == cfg.numLayers)) = false :=
        Bool.eq_false_iff.mpr hG
      simp only [hFalse, Bool.not_false, ↓reduceIte] at hVer
      exact absurd hVer (by simp)
  let leafGlobalIdx := (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).1
  let forsIndices   := (corduroyHashMsgWith eng cfg sigStar.rRand pk msgStar).2.1
  match hFOpt : corduroyRecoverForsPkWith eng cfg pk.pkSeed leafGlobalIdx forsIndices sigStar.forsOpenings with
  | none =>
    False.elim (by
      obtain ⟨_, _, _, hRec, _⟩ := hUnpackVer
      rw [hFOpt] at hRec
      exact absurd hRec (by simp))
  | some forsPkStar =>
    if hForsPkNe : forsPkStar ≠ corduroyHonestForsPkWith eng cfg sk leafGlobalIdx then
      have hLayersPos : 0 < sigStar.layerSigs.length := by
        have hWf := hUnpackVer.1
        unfold CorduroyParams.wellFormed at hWf
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
        have hPos : 0 < cfg.numLayers := hWf.1.1.1.1.1.1.1.2
        rw [hUnpackVer.2.1]
        exact hPos
      have hLeafLt : leafGlobalIdx < 2 ^ (sigStar.layerSigs.length * cfg.subtreeHeight) := by
        rw [hUnpackVer.2.1]
        exact (corduroyHashMsgWith_bounds eng cfg sigStar.rRand pk msgStar).1
      have hHypEq : corduroyVerifyHypertreeWith eng cfg pk 0 leafGlobalIdx forsPkStar sigStar.layerSigs =
          some (corduroyHonestSubtreeRootWith eng cfg sk (cfg.numLayers - 1) 0) := by
        obtain ⟨_, _, fp, hRec, hHyp⟩ := hUnpackVer
        rw [hFOpt] at hRec
        injection hRec with hFpEq
        subst hFpEq
        have hPkRt : pk.pkRoot = corduroyHonestSubtreeRootWith eng cfg sk (cfg.numLayers - 1) 0 := by
          rw [hPk]; rfl
        rw [hPkRt] at hHyp
        exact hHyp
      match extractHypertreeDivergenceWith eng cfg sk pk hPk hUnpackVer.1 hFullDigits queries hHonQ
              sigStar.layerSigs 0 leafGlobalIdx forsPkStar hLayersPos
              (by rw [Nat.zero_add]; exact hUnpackVer.2.1) hLeafLt
              (by simp only [↓reduceIte]; exact hForsPkNe) hHypEq with
      | .inl col => .spongeTweakCollision col
      | .inr pre => .wotsChainPreimage pre
    else
      have hForsPkEq : forsPkStar = corduroyHonestForsPkWith eng cfg sk leafGlobalIdx :=
        Decidable.of_not_not hForsPkNe
      match hTreesOpt : corduroyVerifyForsTreesWith eng cfg pk.pkSeed leafGlobalIdx 0 forsIndices sigStar.forsOpenings with
      | none =>
        False.elim (by
          unfold corduroyRecoverForsPkWith at hFOpt
          by_cases hG : (forsIndices.length == cfg.forsTrees && sigStar.forsOpenings.length == cfg.forsTrees) = true
          · simp only [hG, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hTreesOpt] at hFOpt
            exact absurd hFOpt (by simp)
          · have hFalse : (forsIndices.length == cfg.forsTrees && sigStar.forsOpenings.length == cfg.forsTrees) = false :=
              Bool.eq_false_iff.mpr hG
            simp only [hFalse, Bool.not_false, ↓reduceIte] at hFOpt
            exact absurd hFOpt (by simp))
      | some rootsStar =>
        have hCompEq : corduroyForsRootsCompressWith eng pk.pkSeed leafGlobalIdx rootsStar = forsPkStar := by
          unfold corduroyRecoverForsPkWith at hFOpt
          by_cases hG : (forsIndices.length == cfg.forsTrees && sigStar.forsOpenings.length == cfg.forsTrees) = true
          · simp only [hG, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hTreesOpt, Option.some.injEq] at hFOpt
            exact hFOpt
          · have hFalse : (forsIndices.length == cfg.forsTrees && sigStar.forsOpenings.length == cfg.forsTrees) = false :=
              Bool.eq_false_iff.mpr hG
            simp only [hFalse, Bool.not_false, ↓reduceIte] at hFOpt
            exact absurd hFOpt (by simp)
        let honRoots := (List.range cfg.forsTrees).map (corduroyHonestForsTreeRootWith eng cfg sk leafGlobalIdx)
        if hRootsNe : rootsStar ≠ honRoots then
          .spongeTweakCollision
            { adrs1 := forsRootsAdrs leafGlobalIdx
              in1   := rootsStar
              adrs2 := forsRootsAdrs leafGlobalIdx
              in2   := honRoots
              distinctTweakOrInput := fun hPair => by
                injection hPair with _ hIn
                exact hRootsNe hIn
              sameSpongeOutput := by
                dsimp only [honRoots, corduroyForsRootsCompressWith, corduroyHonestForsPkWith] at hCompEq hForsPkEq ⊢
                rw [hSeed] at hCompEq ⊢
                exact hCompEq.trans hForsPkEq }
        else
          have hRootsEq : rootsStar = honRoots := Decidable.of_not_not hRootsNe
          have hForsIdxLen : forsIndices.length = cfg.forsTrees :=
            (corduroyHashMsgWith_bounds eng cfg sigStar.rRand pk msgStar).2.1
          have hRootsShift : rootsStar =
              ((List.range forsIndices.length).map fun t =>
                corduroyHonestForsTreeRootWith eng cfg sk leafGlobalIdx (0 + t)) := by
            rw [hRootsEq, hForsIdxLen]
            apply List.map_congr_left
            intro t _
            rw [Nat.zero_add]
          match extractForsTreesCollisionOrSecretsWith eng cfg sk pk.pkSeed hSeed leafGlobalIdx
                  forsIndices sigStar.forsOpenings rootsStar 0 hTreesOpt hRootsShift with
          | .inl col => .spongeTweakCollision col
          | .inr hAllSec =>
            match hCollSearch : findCollidingMsgHashQueryWith eng cfg pk leafGlobalIdx forsIndices queries with
            | some ⟨q, hqMem, hSameLeaf, hSameDigest⟩ =>
              .msgHashCollision
                { r1   := sigStar.rRand
                  pk1  := pk
                  msg1 := msgStar
                  r2   := q.sig.rRand
                  pk2  := pk
                  msg2 := q.msg
                  distinctInputs := fun hEq => by
                    injection hEq with _ hTail
                    injection hTail with _ hMsgEq
                    rw [hMsgEq] at hFresh
                    exact hFresh (List.mem_map.mpr ⟨q, hqMem, rfl⟩)
                  sameLeafIdx   := hSameLeaf.symm
                  sameMsgDigest := hSameDigest.symm }
            | none =>
              have hNoColl := findCollidingMsgHashQueryWith_none eng cfg pk leafGlobalIdx forsIndices queries hCollSearch
              have hUncovEx : ∃ k, k < forsIndices.length ∧
                  ∀ q ∈ queries,
                    (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 = leafGlobalIdx →
                    (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).2.1.getD k 0 ≠ forsIndices.getD k 0 := by
                rcases hForsRes with ⟨q, hqMem, h1, h2⟩ | hEx
                · exact False.elim (hNoColl q hqMem ⟨h1, h2⟩)
                · exact hEx
              let ⟨j, hjLt, _⟩ := findBoundedDecidableWitness
                (fun k => ∀ q ∈ queries,
                  (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).1 = leafGlobalIdx →
                  (corduroyHashMsgWith eng cfg q.sig.rRand pk q.msg).2.1.getD k 0 ≠ forsIndices.getD k 0)
                forsIndices.length hUncovEx
              let candSec := (sigStar.forsOpenings.getD j { secretVal := lane4Zero, authPath := [] }).secretVal
              let idxJ := forsIndices.getD j 0
              have hSecMatch : candSec = corduroyForsSecretWith eng sk leafGlobalIdx j idxJ := by
                have hM := hAllSec j hjLt
                rw [Nat.zero_add] at hM
                exact hM
              .wotsChainPreimage
                { adrs := forsLeafAdrs leafGlobalIdx j idxJ
                  dStar := 0
                  dHonest := 1
                  candAtDStar := candSec
                  preimageLink := candSec
                  targetLink := corduroyHonestForsLeafWith eng sk leafGlobalIdx j idxJ
                  stepStrictlyEarlier := Nat.zero_lt_one
                  spongePreimageEq := by
                    change corduroyForsLeafHashWith eng sk.pkSeed leafGlobalIdx j idxJ candSec = _
                    rw [hSecMatch]
                    rfl
                  honestChainMatch := Or.inr ⟨leafGlobalIdx, j, idxJ, rfl, rfl, rfl, rfl, hSecMatch, rfl⟩ }

/-- **Theorem 2: Constructive `Corduroy` Multi-Target EUF-CMA Witness Extractor (`corduroy_euf_cma_extract`)**:
    Given `q_sig` honest signing queries `queries` and ANY valid `Corduroy` forgery `(msgStar, sigStar)`
    on a fresh message `msgStar ∉ queries.map (·.msg)` (under standard multi-target FORS non-covering
    `CorduroyForsUncoveredOrColliding`, which holds unconditionally whenever `≤ 1` query hit `leafGlobalIdx*`),
    constructively (`Type`-valued, `0 Classical.choice`) extracts an explicit break of ONE of three
    concrete `Poseidon2`/sponge problems:
    - `CorduroyBreak.msgHashCollision`: distinct `(R, pk, msg) ≠ (R', pk', msg')` mapping to the same leaf index + message digest;
    - `CorduroyBreak.spongeTweakCollision`: distinct `(adrs1, in1) ≠ (adrs2, in2)` producing the same 4-Goldilocks-limb sponge output;
    - `CorduroyBreak.wotsChainPreimage`: explicit chain link inversion `d* < d_honest` via `targetSum` conservation. -/
def corduroy_euf_cma_extract
    (cfg : CorduroyParams) (sk : CorduroySecretKey) (pk : CorduroyPublicKey)
    (queries : List CorduroySignedQuery)
    (msgStar : Lane4) (sigStar : CorduroySig)
    (hPk : pk = corduroyDerivePk cfg sk)
    (hFullDigits : cfg.wotsChains = 128)
    (hHonQ : CorduroyQuerySetHonest cfg sk queries)
    (hFresh : msgStar ∉ queries.map (·.msg))
    (hVer : corduroyVerify cfg pk msgStar sigStar = true)
    (hForsRes : CorduroyForsUncoveredOrColliding cfg pk queries
      (corduroyHashMsg cfg sigStar.rRand pk msgStar).1
      (corduroyHashMsg cfg sigStar.rRand pk msgStar).2.1) :
    CorduroyBreak cfg pk sk :=
  (corduroy_euf_cma_extract_with corduroyPoseidon2Engine cfg sk pk queries msgStar sigStar
    hPk hFullDigits hHonQ hFresh hVer hForsRes).toCanonical

/-- `PSum`-formatted view of `corduroy_euf_cma_extract` (`0 Classical.choice`). -/
def corduroy_euf_cma_extract_psum
    (cfg : CorduroyParams) (sk : CorduroySecretKey) (pk : CorduroyPublicKey)
    (queries : List CorduroySignedQuery)
    (msgStar : Lane4) (sigStar : CorduroySig)
    (hPk : pk = corduroyDerivePk cfg sk)
    (hFullDigits : cfg.wotsChains = 128)
    (hHonQ : CorduroyQuerySetHonest cfg sk queries)
    (hFresh : msgStar ∉ queries.map (·.msg))
    (hVer : corduroyVerify cfg pk msgStar sigStar = true)
    (hForsRes : CorduroyForsUncoveredOrColliding cfg pk queries
      (corduroyHashMsg cfg sigStar.rRand pk msgStar).1
      (corduroyHashMsg cfg sigStar.rRand pk msgStar).2.1) :
    PSum (CorduroyMsgHashCollision cfg)
      (PSum (CorduroySpongeTweakCollision pk.pkSeed) (CorduroyWotsChainPreimage sk)) :=
  (corduroy_euf_cma_extract cfg sk pk queries msgStar sigStar
    hPk hFullDigits hHonQ hFresh hVer hForsRes).toPSum

/-- Unconditional corollary of `corduroy_euf_cma_extract` whenever at most 1 query hit `leafGlobalIdx*`
    (e.g., `1`-CMA or distinct-leaf `q_sig`-CMA — zero FORS subset-covering premise required!). -/
def corduroy_euf_cma_extract_distinct_leaves
    (cfg : CorduroyParams) (sk : CorduroySecretKey) (pk : CorduroyPublicKey)
    (queries : List CorduroySignedQuery)
    (msgStar : Lane4) (sigStar : CorduroySig)
    (hPk : pk = corduroyDerivePk cfg sk)
    (hFullDigits : cfg.wotsChains = 128)
    (hHonQ : CorduroyQuerySetHonest cfg sk queries)
    (hFresh : msgStar ∉ queries.map (·.msg))
    (hVer : corduroyVerify cfg pk msgStar sigStar = true)
    (hAtMostOneLeafHit : (queries.filter (fun q =>
      (corduroyHashMsg cfg q.sig.rRand pk q.msg).1 ==
        (corduroyHashMsg cfg sigStar.rRand pk msgStar).1)).length ≤ 1) :
    CorduroyBreak cfg pk sk :=
  have hWf : cfg.wellFormed = true := by
    unfold corduroyVerify corduroyVerifyWith at hVer
    by_cases hG : (cfg.wellFormed && (sigStar.layerSigs.length == cfg.numLayers)) = true
    · simp only [Bool.and_eq_true] at hG; exact hG.1
    · have hF : (cfg.wellFormed && (sigStar.layerSigs.length == cfg.numLayers)) = false :=
        Bool.eq_false_iff.mpr hG
      simp only [hF, Bool.not_false, ↓reduceIte] at hVer
      exact absurd hVer (by simp)
  have hForsPos : 0 < cfg.forsTrees := by
    unfold CorduroyParams.wellFormed at hWf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
    exact hWf.1.1.1.2
  have hForsLen : (corduroyHashMsg cfg sigStar.rRand pk msgStar).2.1.length = cfg.forsTrees :=
    (corduroyHashMsg_bounds cfg sigStar.rRand pk msgStar).2.1
  corduroy_euf_cma_extract cfg sk pk queries msgStar sigStar hPk hFullDigits hHonQ hFresh hVer
    (corduroy_single_leaf_hit_uncovered_with corduroyPoseidon2Engine cfg pk queries _ _
      hForsPos hForsLen hAtMostOneLeafHit)

/-! ## §3. Full Deployed 256-Column `Hem` `StepOp` AIR Completeness, Constructive Extraction & WHIR Wiring -/

section HemStepOp256Machine

local infixl:65 " +ₚ " => Goldilocks.add
local infixl:65 " -ₚ " => Goldilocks.sub
local infixl:70 " *ₚ " => Goldilocks.mul
local notation "‹" n "›" => Goldilocks.ofNat n

private theorem g_add_zero (a : Goldilocks) : a +ₚ Goldilocks.zero = a :=
  LawfulCommRing.add_zero a
private theorem g_zero_add (a : Goldilocks) : Goldilocks.zero +ₚ a = a :=
  LawfulCommRing.zero_add a
private theorem g_add_assoc (a b c : Goldilocks) : (a +ₚ b) +ₚ c = a +ₚ (b +ₚ c) :=
  LawfulCommRing.add_assoc a b c
private theorem g_add_comm (a b : Goldilocks) : a +ₚ b = b +ₚ a :=
  LawfulCommRing.add_comm a b
private theorem g_mul_zero (a : Goldilocks) : a *ₚ Goldilocks.zero = Goldilocks.zero :=
  LawfulCommRing.mul_zero a
private theorem g_zero_mul (a : Goldilocks) : Goldilocks.zero *ₚ a = Goldilocks.zero :=
  LawfulCommRing.zero_mul a
private theorem g_mul_one (a : Goldilocks) : a *ₚ Goldilocks.one = a :=
  LawfulCommRing.mul_one a
private theorem g_one_mul (a : Goldilocks) : Goldilocks.one *ₚ a = a :=
  LawfulCommRing.one_mul a
private theorem g_mul_assoc (a b c : Goldilocks) : (a *ₚ b) *ₚ c = a *ₚ (b *ₚ c) :=
  LawfulCommRing.mul_assoc a b c
private theorem g_mul_comm (a b : Goldilocks) : a *ₚ b = b *ₚ a :=
  LawfulCommRing.mul_comm a b
private theorem g_left_distrib (a b c : Goldilocks) : a *ₚ (b +ₚ c) = (a *ₚ b) +ₚ (a *ₚ c) :=
  LawfulCommRing.left_distrib a b c
private theorem g_sub_self (a : Goldilocks) : a -ₚ a = Goldilocks.zero :=
  LawfulCommRing.sub_self a
private theorem g_sub_eq_zero_iff {a b : Goldilocks} : a -ₚ b = Goldilocks.zero ↔ a = b :=
  LawfulCommRing.sub_eq_zero_iff
private theorem g_ofNat_add (a b : Nat) : Goldilocks.ofNat (a + b) = ‹a› +ₚ ‹b› := by
  apply Goldilocks.ext
  rw [Goldilocks.ofNat_val, Goldilocks.add_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val,
      Nat.add_mod]
private theorem g_ofNat_mul (a b : Nat) : Goldilocks.ofNat (a * b) = ‹a› *ₚ ‹b› := by
  apply Goldilocks.ext
  rw [Goldilocks.ofNat_val, Goldilocks.mul_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val,
      Nat.mul_mod]

/-! ### §3.1. Polymorphic No-Wrap Backward-Unpacking & `< 2^63` Limb Decomposition Lemmas -/

/-- Evaluate a little-endian digit list in base `B`: `d_0 + B * (d_1 + B * ...)`. -/
def evalBaseDigits (B : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + B * evalBaseDigits B ds

theorem evalBaseDigits_lt_pow (B : Nat) (hB : 0 < B) :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < B) → evalBaseDigits B ds < B ^ ds.length
  | [], _ => by simp [evalBaseDigits]
  | d :: ds, hLt => by
    have hd : d < B := hLt d (List.mem_cons_self ..)
    have ih := evalBaseDigits_lt_pow B hB ds (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    dsimp only [evalBaseDigits, List.length_cons]
    rw [Nat.pow_succ, Nat.mul_comm _ B]
    have hLe : 1 + evalBaseDigits B ds ≤ B ^ ds.length := by omega
    calc d + B * evalBaseDigits B ds
      _ < B + B * evalBaseDigits B ds := Nat.add_lt_add_right hd _
      _ = B * (1 + evalBaseDigits B ds) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ B * B ^ ds.length := Nat.mul_le_mul_left B hLe

theorem evalBaseDigits_inj (B : Nat) (hB : 0 < B) :
    ∀ {ds1 ds2 : List Nat},
      ds1.length = ds2.length →
      (∀ d ∈ ds1, d < B) →
      (∀ d ∈ ds2, d < B) →
      evalBaseDigits B ds1 = evalBaseDigits B ds2 →
      ds1 = ds2
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hLen, _, _, _ => False.elim (Nat.succ_ne_zero _ hLen.symm)
  | _ :: _, [], hLen, _, _, _ => False.elim (Nat.succ_ne_zero _ hLen)
  | d1 :: r1, d2 :: r2, hLen, hLt1, hLt2, hEq => by
    have hd1 : d1 < B := hLt1 d1 (List.mem_cons_self ..)
    have hd2 : d2 < B := hLt2 d2 (List.mem_cons_self ..)
    dsimp only [evalBaseDigits] at hEq
    have hMod := congrArg (· % B) hEq
    rw [Nat.mul_comm B (evalBaseDigits B r1), Nat.mul_comm B (evalBaseDigits B r2),
        Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hd1, Nat.mod_eq_of_lt hd2] at hMod
    subst hMod
    have hCancel := Nat.add_left_cancel hEq
    have hSubEq : evalBaseDigits B r1 = evalBaseDigits B r2 :=
      Nat.eq_of_mul_eq_mul_left hB hCancel
    rw [evalBaseDigits_inj B hB (Nat.succ.inj hLen)
          (fun x hx => hLt1 x (List.mem_cons_of_mem _ hx))
          (fun x hx => hLt2 x (List.mem_cons_of_mem _ hx)) hSubEq]

/-- Multi-step in-field quotient-unpacking chain `p_m = ofNat d_m +ₚ (p_{m+1} *ₚ ofNat B)` ending at `qFinal`.
    Instantiates simultaneously to:
    - FORS index unpacking (`B = 256, k ≤ 6`, `256^6 = 2^48 < p`),
    - WOTS remaining-step unpacking (`B = 4, k ≤ 26`, `4^26 = 2^52 < p`),
    - FORS & XMSS Merkle cursor halving (`B = 2, k ∈ {4, 6, 8}`, `2^8 = 256 < p`). -/
def UnpackChain (B : Nat) : Goldilocks → List Nat → Goldilocks → Prop
  | pEnd, [], qFinal => pEnd = qFinal
  | pCur, d :: rest, qFinal =>
    d < B ∧ ∃ pNext : Goldilocks,
      pCur = Goldilocks.ofNat d +ₚ (pNext *ₚ ‹B›) ∧
      UnpackChain B pNext rest qFinal

/-- **No-Wrap Backward-Unpacking Theorem (`baseBUnpackChain_backward`)**:
    Whenever an `UnpackChain B p0 ds Goldilocks.zero` ends at `0` with `B ^ ds.length < goldilocksPrime`,
    every intermediate field quotient is automatically canonical (`< B ^ (k - m) < p`, with ZERO
    need for separate per-row quotient range checks!) and `p0.val = evalBaseDigits B ds`. -/
theorem baseBUnpackChain_backward (B : Nat) (hB : 0 < B) :
    ∀ (ds : List Nat) (p0 : Goldilocks),
      B ^ ds.length < goldilocksPrime →
      UnpackChain B p0 ds Goldilocks.zero →
      p0.val = evalBaseDigits B ds ∧ p0.val < B ^ ds.length ∧ (∀ d ∈ ds, d < B)
  | [], p0, _, hChain => by
    dsimp only [UnpackChain] at hChain
    subst hChain
    exact ⟨rfl, by simp [Goldilocks.zero], fun _ h => False.elim (List.not_mem_nil h)⟩
  | d :: rest, p0, hPowLtP, hChain => by
    rcases hChain with ⟨hd, pNext, hp0, hSub⟩
    have hSubPowLe : B ^ rest.length ≤ B ^ (d :: rest).length :=
      Nat.pow_le_pow_right hB (Nat.le_succ _)
    have hBLtP : B < goldilocksPrime := by
      have hB1 : B ^ 1 ≤ B ^ (d :: rest).length :=
        Nat.pow_le_pow_right hB (by simp)
      rw [Nat.pow_one] at hB1
      exact Nat.lt_of_le_of_lt hB1 hPowLtP
    obtain ⟨hNextVal, hNextLt, hRestLt⟩ :=
      baseBUnpackChain_backward B hB rest pNext (Nat.lt_of_le_of_lt hSubPowLe hPowLtP) hSub
    have hdVal : (Goldilocks.ofNat d).val = d :=
      Nat.mod_eq_of_lt (Nat.lt_trans hd hBLtP)
    have hBVal : (Goldilocks.ofNat B).val = B :=
      Nat.mod_eq_of_lt hBLtP
    have hCombLt : d + pNext.val * B < B ^ (d :: rest).length := by
      dsimp only [List.length_cons]
      rw [Nat.pow_succ]
      have hLe : pNext.val + 1 ≤ B ^ rest.length := hNextLt
      calc d + pNext.val * B
        _ < B + pNext.val * B := Nat.add_lt_add_right hd _
        _ = (pNext.val + 1) * B := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        _ ≤ B ^ rest.length * B := Nat.mul_le_mul_right B hLe
    have hMulVal : (pNext *ₚ ‹B›).val = B * evalBaseDigits B rest := by
      rw [Goldilocks.mul_val, hBVal, Nat.mod_eq_of_lt
            (Nat.lt_of_le_of_lt (Nat.le_add_left _ d) (Nat.lt_trans hCombLt hPowLtP)),
          hNextVal, Nat.mul_comm]
    have hAddLtP : d + B * evalBaseDigits B rest < goldilocksPrime := by
      rw [Nat.mul_comm B, ← hNextVal]
      exact Nat.lt_trans hCombLt hPowLtP
    have hp0Val : p0.val = evalBaseDigits B (d :: rest) := by
      rw [hp0, Goldilocks.add_val, hdVal, hMulVal, Nat.mod_eq_of_lt hAddLtP]
      rfl
    refine ⟨hp0Val, ?_, ?_⟩
    · rw [hp0Val, evalBaseDigits, Nat.mul_comm B, ← hNextVal]
      exact hCombLt
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hTail
      · exact hd
      · exact hRestLt x hTail

theorem extractLimbBase4Digits_getElem :
    ∀ (count v i : Nat) (hi : i < (extractLimbBase4Digits count v).length),
      (extractLimbBase4Digits count v)[i]'hi = (v / 4 ^ i) % 4
  | 0, _, _, hi => False.elim (by simp [extractLimbBase4Digits] at hi)
  | _ + 1, v, 0, _ => by simp [extractLimbBase4Digits]
  | count + 1, v, i + 1, hi => by
    have hi' : i < (extractLimbBase4Digits count (v / 4)).length := by
      rw [extractLimbBase4Digits_length] at hi ⊢
      omega
    have hStep : (extractLimbBase4Digits (count + 1) v)[i + 1]'hi =
        (extractLimbBase4Digits count (v / 4))[i]'hi' := rfl
    rw [hStep, extractLimbBase4Digits_getElem count (v / 4) i hi',
        Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 4]

private theorem evalGoldilocksBase4_snoc :
    ∀ (xs : List Goldilocks) (y : Goldilocks),
      evalGoldilocksBase4 (xs ++ [y]) =
        evalGoldilocksBase4 xs +ₚ (y *ₚ ‹4 ^ xs.length›)
  | [], y => by
    show y +ₚ (‹4› *ₚ Goldilocks.zero) = Goldilocks.zero +ₚ (y *ₚ ‹1›)
    have h1 : (‹1› : Goldilocks) = Goldilocks.one := Goldilocks.ext rfl
    rw [h1, g_mul_zero, g_add_zero, g_zero_add, g_mul_one]
  | x :: xs, y => by
    show x +ₚ (‹4› *ₚ evalGoldilocksBase4 (xs ++ [y])) =
      (x +ₚ (‹4› *ₚ evalGoldilocksBase4 xs)) +ₚ (y *ₚ ‹4 ^ (xs.length + 1)›)
    rw [evalGoldilocksBase4_snoc xs y, g_left_distrib, g_add_assoc]
    congr 1
    have hPow : (‹4 ^ (xs.length + 1)› : Goldilocks) = ‹4› *ₚ ‹4 ^ xs.length› := by
      rw [Nat.pow_succ, Nat.mul_comm]
      exact g_ofNat_mul 4 (4 ^ xs.length)
    rw [hPow, ← g_mul_assoc, g_mul_comm ‹4› y, g_mul_assoc]

private theorem stepWeightedSum_pow4_eq_evalGoldilocksBase4 (f : Nat → Goldilocks) :
    ∀ (n : Nat),
      stepWeightedSum f (fun i => 4 ^ i) n = evalGoldilocksBase4 ((List.range n).map f)
  | 0 => rfl
  | n + 1 => by
    unfold stepWeightedSum
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.map_append, List.map_cons, List.map_nil, evalGoldilocksBase4_snoc,
        List.length_map, List.length_range]
    exact congrArg (· +ₚ (f n *ₚ ‹4 ^ n›)) (stepWeightedSum_pow4_eq_evalGoldilocksBase4 f n)

theorem stepBoolCheck_eq_zero_iff (b : Goldilocks) :
    stepBoolCheck b = Goldilocks.zero ↔ (b = Goldilocks.zero ∨ b = Goldilocks.one) := by
  unfold stepBoolCheck
  constructor
  · intro h
    have h' : CommRingOps.mul b (Goldilocks.one -ₚ b) = CommRingOps.zero := h
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h' with h0 | h1
    · exact .inl h0
    · exact .inr (g_sub_eq_zero_iff.mp h1).symm
  · rintro (rfl | rfl)
    · exact g_zero_mul _
    · rw [g_sub_self, g_mul_zero]

/-- Canonical `< 2^63` base-4 characterization of `stepLimb63Decomp`. -/
theorem stepLimb63Decomp_allZero_iff (x : StepOpRowInputs) (l : Nat) :
    allZeroGoldilocks (stepLimb63Decomp x l) = true ↔
      (x.prev (stMainSponge + l)).val < 2 ^ 63 ∧
      (∀ i < 31, x.aux i = Goldilocks.ofNat (((x.prev (stMainSponge + l)).val / 4 ^ i) % 4)) ∧
      x.aux 31 = Goldilocks.ofNat ((x.prev (stMainSponge + l)).val / 4 ^ 31) := by
  let v := x.prev (stMainSponge + l)
  let w : Limb63DecompWitness :=
    { limbVal := v
      digits  := (List.range 31).map x.aux
      topBit  := x.aux 31 }
  have hPow62 : (‹2 ^ 62› : Goldilocks) = ‹4 ^ 31› := rfl
  have hTail2 : ∀ (r0 r1 : Goldilocks),
      allZeroGoldilocks [r0, r1] = ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero)) := by
    intros; simp [allZeroGoldilocks]
  have hHead3 : ∀ (r0 r1 r2 : Goldilocks) (rest : List Goldilocks),
      allZeroGoldilocks ([r0, r1, r2] ++ rest) =
        ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero) &&
         (r2 == Goldilocks.zero) && allZeroGoldilocks rest) := by
    intros; simp [allZeroGoldilocks, Bool.and_assoc]
  have hEquiv : allZeroGoldilocks (stepLimb63Decomp x l) = true ↔
      allZeroGoldilocks (limb63DecompResiduals v w) = true := by
    unfold stepLimb63Decomp limb63DecompResiduals
    dsimp only [w]
    have hLen : (((List.range 31).map x.aux).length == 31) = true := by simp
    rw [hLen, List.map_map]
    simp only [↓reduceIte, allZeroGoldilocks_append, hTail2, hHead3, Bool.and_eq_true,
      beq_iff_eq, g_sub_self, true_and, stepBoolCheck_eq_zero_iff,
      boolBitResidual_eq_zero_iff, g_sub_eq_zero_iff,
      stepWeightedSum_pow4_eq_evalGoldilocksBase4, hPow62]
    have hMapEq : ((List.range 31).map (quarticBase4 ∘ x.aux)) =
        (List.range 31).map (fun i => quarticBase4 (x.aux i)) := rfl
    rw [hMapEq]
    constructor
    · rintro ⟨hQuart, hBit, hEq⟩
      refine ⟨⟨hBit, ?_⟩, hQuart⟩
      rw [g_mul_comm (‹4 ^ 31›) (x.aux 31)]
      exact hEq.symm
    · rintro ⟨⟨hBit, hEq⟩, hQuart⟩
      refine ⟨hQuart, hBit, ?_⟩
      rw [g_mul_comm (x.aux 31) (‹4 ^ 31›)]
      exact hEq.symm
  rw [hEquiv, limb63DecompResiduals_allZero_iff]
  constructor
  · rintro ⟨hLt, hWEq⟩
    have hDigEq := congrArg Limb63DecompWitness.digits hWEq
    have hTopEq := congrArg Limb63DecompWitness.topBit hWEq
    dsimp only [w, honestLimb63DecompWitness] at hDigEq hTopEq
    refine ⟨hLt, fun i hi => ?_, hTopEq⟩
    have hGet := congrArg (fun ls => ls.getD i Goldilocks.zero) hDigEq
    have hiL1 : i < ((List.range 31).map x.aux).length := by simp [hi]
    have hiExt : i < (extractLimbBase4Digits 31 v.val).length := by
      rw [extractLimbBase4Digits_length]; exact hi
    have hiL2 : i < ((extractLimbBase4Digits 31 v.val).map Goldilocks.ofNat).length := by
      simp [hiExt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL1, Option.getD_some,
        List.getElem_map, List.getElem_range,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiL2, Option.getD_some,
        List.getElem_map, extractLimbBase4Digits_getElem 31 v.val i hiExt] at hGet
    exact hGet
  · rintro ⟨hLt, hAux, hTop⟩
    refine ⟨hLt, ?_⟩
    dsimp only [w, honestLimb63DecompWitness]
    rw [hTop]
    congr 1
    apply List.ext_getElem
    · simp [extractLimbBase4Digits_length]
    · intro i hi1 hi2
      have hi31 : i < 31 := by simpa using hi1
      have hiExt : i < (extractLimbBase4Digits 31 v.val).length := by
        rw [extractLimbBase4Digits_length]; exact hi31
      rw [List.getElem_map, List.getElem_range, List.getElem_map,
          extractLimbBase4Digits_getElem 31 v.val i hiExt]
      exact hAux i hi31

theorem stepByteVal_eq_of_limb63 (x : StepOpRowInputs) (l sub : Nat)
    (hSub : sub < 7)
    (hDecomp : allZeroGoldilocks (stepLimb63Decomp x l) = true) :
    stepByteVal x sub =
      Goldilocks.ofNat (((x.prev (stMainSponge + l)).val / 256 ^ sub) % 256) := by
  obtain ⟨_, hAux, _⟩ := (stepLimb63Decomp_allZero_iff x l).mp hDecomp
  let v := (x.prev (stMainSponge + l)).val
  have e0 := hAux (4 * sub) (by omega)
  have e1 := hAux (4 * sub + 1) (by omega)
  have e2 := hAux (4 * sub + 2) (by omega)
  have e3 := hAux (4 * sub + 3) (by omega)
  unfold stepByteVal
  rw [e0, e1, e2, e3]
  simp only [← g_ofNat_mul, ← g_ofNat_add]
  apply congrArg Goldilocks.ofNat
  have hPow0 : 4 ^ (4 * sub) = 256 ^ sub := by
    rw [Nat.pow_mul]
  have hPow1 : 4 ^ (4 * sub + 1) = 256 ^ sub * 4 := by
    rw [Nat.pow_add, hPow0]
  have hPow2 : 4 ^ (4 * sub + 2) = 256 ^ sub * 16 := by
    rw [Nat.pow_add, hPow0]
  have hPow3 : 4 ^ (4 * sub + 3) = 256 ^ sub * 64 := by
    rw [Nat.pow_add, hPow0]
  rw [hPow0, hPow1, hPow2, hPow3,
      ← Nat.div_div_eq_div_mul v (256 ^ sub) 4,
      ← Nat.div_div_eq_div_mul v (256 ^ sub) 16,
      ← Nat.div_div_eq_div_mul v (256 ^ sub) 64]
  generalize v / 256 ^ sub = w
  omega

theorem stepLow4Bits_eq_of_limb63 (x : StepOpRowInputs) (l : Nat)
    (hDecomp : allZeroGoldilocks (stepLimb63Decomp x l) = true) :
    x.aux 0 +ₚ (x.aux 1 *ₚ ‹4›) =
      Goldilocks.ofNat ((x.prev (stMainSponge + l)).val % 16) := by
  obtain ⟨_, hAux, _⟩ := (stepLimb63Decomp_allZero_iff x l).mp hDecomp
  rw [hAux 0 (by decide), hAux 1 (by decide)]
  simp only [← g_ofNat_mul, ← g_ofNat_add, Nat.pow_zero, Nat.pow_one, Nat.div_one]
  apply congrArg Goldilocks.ofNat
  omega

private theorem evalBase4Digits_map_div_mod :
    ∀ (n w : Nat),
      evalBase4Digits ((List.range n).map (fun i => (w / 4 ^ i) % 4)) = w % (4 ^ n)
  | 0, w => by simp [evalBase4Digits, Nat.mod_one]
  | n + 1, w => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    dsimp only [evalBase4Digits]
    have hShift :
        (List.range n).map ((fun i => (w / 4 ^ i) % 4) ∘ Nat.succ) =
        (List.range n).map (fun i => ((w / 4) / 4 ^ i) % 4) := by
      congr 1; funext i
      dsimp only [Function.comp]
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 4]
    rw [hShift, evalBase4Digits_map_div_mod n (w / 4), Nat.pow_zero, Nat.div_one, Nat.pow_succ]
    have hPowPos : 0 < 4 ^ n := Nat.pow_pos (by decide)
    have hRemLt : (w / 4) % 4 ^ n < 4 ^ n := Nat.mod_lt _ hPowPos
    have hW : w = (w % 4 + 4 * ((w / 4) % 4 ^ n)) + ((w / 4) / 4 ^ n) * (4 ^ n * 4) := by
      have h1 := (Nat.mod_add_div w 4).symm
      have h2 := (Nat.mod_add_div (w / 4) (4 ^ n)).symm
      calc w
        _ = w % 4 + 4 * (w / 4) := h1
        _ = w % 4 + 4 * ((w / 4) % 4 ^ n + 4 ^ n * ((w / 4) / 4 ^ n)) := by rw [← h2]
        _ = (w % 4 + 4 * ((w / 4) % 4 ^ n)) + ((w / 4) / 4 ^ n) * (4 ^ n * 4) := by
          rw [Nat.mul_add, Nat.add_assoc]
          congr 1
          rw [← Nat.mul_assoc, Nat.mul_comm (4 * 4 ^ n), Nat.mul_comm 4 (4 ^ n)]
    conv => rhs; rw [hW, Nat.add_mul_mod_self_right]
    exact (Nat.mod_eq_of_lt (by omega)).symm

theorem stepHi28_eq_of_limb63 (x : StepOpRowInputs) (l : Nat)
    (hDecomp : allZeroGoldilocks (stepLimb63Decomp x l) = true) :
    stepHi28 x = Goldilocks.ofNat (((x.prev (stMainSponge + l)).val % 2 ^ 32) / 16) := by
  obtain ⟨_, hAux, _⟩ := (stepLimb63Decomp_allZero_iff x l).mp hDecomp
  let v := (x.prev (stMainSponge + l)).val
  unfold stepHi28
  rw [stepWeightedSum_pow4_eq_evalGoldilocksBase4]
  let ds := (List.range 14).map (fun i => x.aux (2 + i))
  have hDsEq : ds = (List.range 14).map (fun i => Goldilocks.ofNat (((v / 16) / 4 ^ i) % 4)) := by
    apply List.ext_getElem
    · simp [ds]
    · intro i hi1 _
      have hi14 : i < 14 := by simpa [ds] using hi1
      simp only [ds, List.getElem_map, List.getElem_range]
      rw [hAux (2 + i) (by omega)]
      apply congrArg Goldilocks.ofNat
      have hPow : 4 ^ (2 + i) = 16 * 4 ^ i := by
        rw [Nat.pow_add]
      rw [hPow, ← Nat.div_div_eq_div_mul]
  have h4LtP : 4 < goldilocksPrime := by decide
  have hDsLt4 : ∀ d ∈ ds, d.val < 4 := by
    rw [hDsEq]
    intro d hd
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
    rw [Goldilocks.ofNat_val, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) h4LtP)]
    exact Nat.mod_lt _ (by decide)
  apply Goldilocks.ext
  rw [evalGoldilocksBase4_val_of_lt4 ds (by simp [ds]) hDsLt4, hDsEq, List.map_map]
  have hMapVal :
      (List.range 14).map (Goldilocks.val ∘ fun i => Goldilocks.ofNat (((v / 16) / 4 ^ i) % 4)) =
      (List.range 14).map (fun i => ((v / 16) / 4 ^ i) % 4) := by
    congr 1; funext i
    dsimp only [Function.comp]
    rw [Goldilocks.ofNat_val]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) h4LtP)
  rw [hMapVal, evalBase4Digits_map_div_mod 14 (v / 16)]
  have hPow14 : (4 : Nat) ^ 14 = 2 ^ 28 := rfl
  have hPow32 : (2 : Nat) ^ 32 = 16 * 2 ^ 28 := rfl
  rw [hPow14]
  have hLtP : (v % 2 ^ 32) / 16 < goldilocksPrime := by
    have : v % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have : (2 : Nat) ^ 28 < goldilocksPrime := by decide
    omega
  rw [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hLtP]
  have hDivMod : (v / 16) % (2 ^ 28) = (v % (16 * 2 ^ 28)) / 16 := by
    have h1 := (Nat.mod_add_div v (16 * 2 ^ 28)).symm
    conv => lhs; rw [h1]
    have hRew : v % (16 * 2 ^ 28) + 16 * 2 ^ 28 * (v / (16 * 2 ^ 28)) =
        v % (16 * 2 ^ 28) + ((2 ^ 28) * (v / (16 * 2 ^ 28))) * 16 := by
      congr 1
      simp only [Nat.mul_assoc, Nat.mul_comm]
    rw [hRew, Nat.add_mul_div_right _ _ (by decide), Nat.add_mul_mod_self_left]
    have hRemLt : (v % (16 * 2 ^ 28)) / 16 < 2 ^ 28 := by
      have : v % (16 * 2 ^ 28) < 16 * 2 ^ 28 := Nat.mod_lt _ (by decide)
      omega
    exact Nat.mod_eq_of_lt hRemLt
  rw [← hPow32] at hDivMod
  exact hDivMod

/-! ### §3.2. Guard/Transition Decomposition & Selector-Muxed 256-Column `StepOp` Equivalence -/

/-- Valid index ranges of parameterized `StepConstraintKind` constructors (`trace.rs`). -/
def StepConstraintKind.validSlot : StepConstraintKind → Bool
  | .statelessDecompLimb l => decide (l < 7)
  | .forsLeafHash slot     => decide (slot < 6)
  | .hmsgDecompLimb l      => decide (l < 5)
  | .wotsChainStep0 slot   => decide (slot < 5)
  | _                      => true

/-- Complete duplicate-free catalog of all 52 `StepConstraintKind` classes of the deployed machine. -/
def allStepConstraintKinds : List StepConstraintKind :=
  [.idle, .statefulHmsgBlock0, .statefulHmsgBlock1, .statefulHmsgSqueeze,
   .statelessDeriveBlock0, .statelessDeriveBlock1] ++
  (List.range 7).map StepConstraintKind.statelessDecompLimb ++
  [.forsRootsSpongeInit] ++
  (List.range 6).map StepConstraintKind.forsLeafHash ++
  [.forsMerkleBlockA,
   .forsMerkleBlockB false false, .forsMerkleBlockB false true,
   .forsMerkleBlockB true false, .forsMerkleBlockB true true,
   .forsRootsPairAbsorb false, .forsRootsPairAbsorb true,
   .forsRootsFinalSqueeze,
   .detTreeHmsgBlock0, .detTreeHmsgBlock1] ++
  (List.range 5).map StepConstraintKind.hmsgDecompLimb ++
  [.wotsTellInit] ++
  (List.range 5).map StepConstraintKind.wotsChainStep0 ++
  [.wotsChainStep1,
   .wotsChainStep2 false, .wotsChainStep2 true,
   .wotsTellPairAbsorb false, .wotsTellPairAbsorb true,
   .wotsTellFinalSqueeze,
   .xmssMerkleBlockA,
   .xmssMerkleBlockB false false, .xmssMerkleBlockB false true,
   .xmssMerkleBlockB true false, .xmssMerkleBlockB true true]

theorem allStepConstraintKinds_nodup : allStepConstraintKinds.Nodup := by
  decide +kernel

theorem allStepConstraintKinds_validSlot :
    ∀ k ∈ allStepConstraintKinds, k.validSlot = true := by
  decide +kernel

private theorem mem_allStepConstraintKinds_of_validSlot (k : StepConstraintKind)
    (h : k.validSlot = true) : k ∈ allStepConstraintKinds := by
  cases k with
  | idle | statefulHmsgBlock0 | statefulHmsgBlock1 | statefulHmsgSqueeze
  | statelessDeriveBlock0 | statelessDeriveBlock1 | forsRootsSpongeInit
  | forsMerkleBlockA | forsRootsFinalSqueeze | detTreeHmsgBlock0 | detTreeHmsgBlock1
  | wotsTellInit | wotsChainStep1 | wotsTellFinalSqueeze | xmssMerkleBlockA =>
    decide +kernel
  | forsMerkleBlockB a b => cases a <;> cases b <;> decide +kernel
  | forsRootsPairAbsorb a => cases a <;> decide +kernel
  | wotsChainStep2 a => cases a <;> decide +kernel
  | wotsTellPairAbsorb a => cases a <;> decide +kernel
  | xmssMerkleBlockB a b => cases a <;> cases b <;> decide +kernel
  | statelessDecompLimb l =>
    have hl : l < 7 := of_decide_eq_true h
    rcases l with _ | _ | _ | _ | _ | _ | _ | l <;> first | decide +kernel | omega
  | forsLeafHash slot =>
    have hs : slot < 6 := of_decide_eq_true h
    rcases slot with _ | _ | _ | _ | _ | _ | slot <;> first | decide +kernel | omega
  | hmsgDecompLimb l =>
    have hl : l < 5 := of_decide_eq_true h
    rcases l with _ | _ | _ | _ | _ | l <;> first | decide +kernel | omega
  | wotsChainStep0 slot =>
    have hs : slot < 5 := of_decide_eq_true h
    rcases slot with _ | _ | _ | _ | _ | slot <;> first | decide +kernel | omega

private theorem wotsPackSlot_lt_5 (chain : Nat) : wotsPackSlot chain < 5 := by
  unfold wotsPackSlot
  split <;> try decide
  split <;> try decide
  split <;> try decide
  split <;> decide

private theorem pushLayerWotsAndMerkle_validSlot (layer subHeight : Nat) (isTopFinal : Bool) :
    ∀ op ∈ pushLayerWotsAndMerkle layer subHeight isTopFinal,
      (stepOpKindAndC0 op).1.validSlot = true := by
  intro op hMem
  unfold pushLayerWotsAndMerkle at hMem
  simp only [List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with ((rfl | ⟨pair, _, ⟨sub, _, rfl | rfl | rfl⟩ | rfl⟩) | rfl) | ⟨lvl, _, rfl | rfl⟩
  · rfl
  · unfold stepOpKindAndC0; exact decide_eq_true (wotsPackSlot_lt_5 _)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem signerProgramBody_validSlot (profile : AggSigProfile) :
    ∀ op ∈ signerProgramBody profile, (stepOpKindAndC0 op).1.validSlot = true := by
  intro op hMem
  cases profile with
  | xmssPoseidon2 =>
    unfold signerProgramBody at hMem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_range] at hMem
    rcases hMem with ((rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | hPush
    · rfl
    · rfl
    · rfl
    · exact decide_eq_true hl
    · exact pushLayerWotsAndMerkle_validSlot 0 6 true op hPush
  | corduroyPoseidon2 =>
    unfold signerProgramBody at hMem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map, List.mem_flatMap, List.mem_range] at hMem
    rcases hMem with (((((rfl | rfl) | ⟨l, hl, rfl⟩) | rfl) | hFors) | rfl) | ⟨layer, _, hLayer⟩
    · rfl
    · rfl
    · exact decide_eq_true hl
    · rfl
    · rcases hFors with ⟨pair, hPair, ⟨sub, hSub, rfl | ⟨lvl, _, rfl | rfl⟩⟩ | rfl⟩
      · exact decide_eq_true (by omega : (2 * pair + sub) / 6 < 6)
      · rfl
      · rfl
      · rfl
    · rfl
    · rcases hLayer with ((rfl | rfl) | ⟨l, hl, rfl⟩) | hPush
      · rfl
      · rfl
      · exact decide_eq_true hl
      · exact pushLayerWotsAndMerkle_validSlot layer 4 (layer + 1 == 16) op hPush

theorem buildSignerProgram_kind_mem_and_valid (profile : AggSigProfile) (t : Nat) :
    (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1 ∈ allStepConstraintKinds ∧
    (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1.validSlot = true := by
  have hVal : (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1.validSlot = true := by
    by_cases ht : t < (buildSignerProgram profile).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
      have hMem := List.getElem_mem ht
      unfold buildSignerProgram at hMem
      rcases List.mem_append.mp hMem with hBody | hRep
      · exact signerProgramBody_validSlot profile _ hBody
      · have hIdle : (buildSignerProgram profile)[t] = StepOp.idle :=
          (List.mem_replicate.mp hRep).2
        rw [hIdle]; rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt ht), Option.getD_none]
      rfl
  exact ⟨mem_allStepConstraintKinds_of_validSlot _ hVal, hVal⟩

/-- Pure guard residuals of `stepMerkleBlockA` (independent of `x.next`). -/
def stepMerkleBlockAGuards (x : StepOpRowInputs) (domainTag meta0 : Goldilocks) : List Goldilocks :=
  [stepBoolCheck (x.aux 0), x.prev stCursorIdx -ₚ ((x.aux 0 +ₚ x.aux 1) +ₚ x.aux 1)] ++
  (List.range 4).flatMap (fun i =>
    [x.stIn i -ₚ x.pkSeed i,
     x.stIn (4 + i) -ₚ
       (((Goldilocks.one -ₚ x.aux 0) *ₚ x.prev (stWork + i)) +ₚ (x.aux 0 *ₚ x.aux (2 + i)))]) ++
  [x.stIn 8 -ₚ domainTag, x.stIn 9 -ₚ meta0, x.stIn 10 -ₚ x.prev stTreeLo,
   x.stIn 11 -ₚ x.prev stTreeHi]

/-- Functional next-state of `stepMerkleBlockA` (independent of `x.next`). -/
def stepMerkleBlockAExpectedNext (x : StepOpRowInputs) (j : Nat) : Goldilocks :=
  if stepInBlock stSubSponge 12 j then x.permOut (j - stSubSponge)
  else if stepInBlock stWork 4 j then
    let i := j - stWork
    (x.aux 0 *ₚ x.prev (stWork + i)) +ₚ ((Goldilocks.one -ₚ x.aux 0) *ₚ x.aux (2 + i))
  else if j = stCursorIdx then x.aux 1
  else x.prev j

/-- Pure pre-state / `stIn` / `permOut` / `aux` guard residuals of one `StepConstraintKind`
    (never reads `x.next`). -/
def stepOpGuardResiduals (kind : StepConstraintKind) (c0 : Goldilocks) (x : StepOpRowInputs) :
    List Goldilocks :=
  match kind with
  | .idle => []
  | .statefulHmsgBlock0 =>
    (List.range 6).map (fun i => stepBoolCheck (x.aux i)) ++
    (List.range 32).map (fun i => stepBoolCheck (x.aux (6 + i))) ++
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgStateful,
     x.stIn 9 -ₚ ((stepWeightedSum x.aux (fun i => 2 ^ i) 6 *ₚ ‹2 ^ 32›) +ₚ
       stepWeightedSum (fun i => x.aux (6 + i)) (fun i => 2 ^ i) 32),
     x.stIn 10 -ₚ x.mu 4, x.stIn 11 -ₚ poseidon2IvTag]
  | .statefulHmsgBlock1 => stepSpongeAbsorbInput x x.aux x.mu
  | .statefulHmsgSqueeze => stepSqueezeInput x
  | .statelessDeriveBlock0 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgStateless, x.stIn 9 -ₚ x.mu 4, x.stIn 10,
     x.stIn 11 -ₚ poseidon2IvTag]
  | .statelessDeriveBlock1 => stepSpongeAbsorbInput x x.aux x.mu
  | .statelessDecompLimb l => stepLimb63Decomp x l
  | .forsRootsSpongeInit =>
    (List.range 4).map (fun i => x.stIn i -ₚ x.pkSeed i) ++
    [x.stIn 4 -ₚ x.prev stKpIdx, x.stIn 5 -ₚ x.prev stTreeLo, x.stIn 6 -ₚ x.prev stTreeHi,
     x.stIn 7 -ₚ ‹32›, x.stIn 8 -ₚ domainForsRoots, x.stIn 9, x.stIn 10,
     x.stIn 11 -ₚ poseidon2IvTag]
  | .forsLeafHash slot =>
    (List.range 4).map (fun k => quarticBase4 (x.aux (4 + k))) ++
    [x.prev (stRemPack + slot) -ₚ
       (stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4 +ₚ (x.aux 8 *ₚ ‹256›))] ++
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.aux i, x.stIn (4 + i) -ₚ x.pkSeed i]) ++
    [x.stIn 8 -ₚ domainForsLeaf,
     x.stIn 9 -ₚ ((x.prev stKpIdx *ₚ ‹2 ^ 24›) +ₚ
       (c0 +ₚ stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4)),
     x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi]
  | .forsMerkleBlockA =>
    stepMerkleBlockAGuards x domainForsNode ((c0 +ₚ (x.prev stKpIdx *ₚ ‹2 ^ 16›)) +ₚ x.aux 1)
  | .forsMerkleBlockB isTreeLast _ =>
    stepMerkleBlockBInput x ++ (if isTreeLast then [x.prev stCursorIdx] else [])
  | .forsRootsPairAbsorb isLastPair =>
    (if isLastPair then (List.range 6).map (fun s => x.prev (stRemPack + s)) else []) ++
    stepSpongeAbsorbInput x (fun i => x.prev (stCurRoot + i)) (fun i => x.prev (stWork + i))
  | .forsRootsFinalSqueeze => stepSqueezeInput x
  | .detTreeHmsgBlock0 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgDetTree, x.stIn 9 -ₚ (c0 +ₚ x.prev stKpIdx),
     x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi]
  | .detTreeHmsgBlock1 =>
    (List.range 32).map (fun i => stepBoolCheck (x.aux i)) ++
    (List.range 4).map (fun i =>
      x.stIn i -ₚ (x.prev (stMainSponge + i) +ₚ x.prev (stCurRoot + i))) ++
    [x.stIn 4 -ₚ (x.prev (stMainSponge + 4) +ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 32),
     x.stIn 5 -ₚ (x.prev (stMainSponge + 5) +ₚ Goldilocks.one)] ++
    (List.range 6).map (fun i => x.stIn (6 + i) -ₚ x.prev (stMainSponge + 6 + i))
  | .hmsgDecompLimb l =>
    stepLimb63Decomp x l ++
    (if l = 4 then [stepHmsgDecompExpected x l stAccOrU1 -ₚ ‹192›] else [])
  | .wotsTellInit =>
    (List.range 4).map (fun i => x.stIn i -ₚ x.pkSeed i) ++
    [x.stIn 4 -ₚ (c0 +ₚ x.prev stKpIdx), x.stIn 5 -ₚ x.prev stTreeLo,
     x.stIn 6 -ₚ x.prev stTreeHi, x.stIn 7 -ₚ ‹128›, x.stIn 8 -ₚ domainWotsPk, x.stIn 9,
     x.stIn 10, x.stIn 11 -ₚ poseidon2IvTag]
  | .wotsChainStep0 slot =>
    [stepBoolCheck (x.aux 4), stepBoolCheck (x.aux 5), stepBoolCheck (x.aux 6),
     x.aux 5 *ₚ (Goldilocks.one -ₚ x.aux 4), x.aux 6 *ₚ (Goldilocks.one -ₚ x.aux 5),
     x.prev (stRemPack + slot) -ₚ
       ((‹3› -ₚ ((x.aux 4 +ₚ x.aux 5) +ₚ x.aux 6)) +ₚ (x.aux 7 *ₚ ‹4›))] ++
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.aux i, x.stIn (4 + i) -ₚ x.pkSeed i]) ++
    stepWotsStepInput x c0
  | .wotsChainStep1 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.prev (stWork + i), x.stIn (4 + i) -ₚ x.pkSeed i]) ++
    stepWotsStepInput x c0
  | .wotsChainStep2 _ =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.prev (stWork + i), x.stIn (4 + i) -ₚ x.pkSeed i]) ++
    stepWotsStepInput x c0
  | .wotsTellPairAbsorb isLastPair =>
    (if isLastPair then (List.range 5).map (fun s => x.prev (stRemPack + s)) else []) ++
    stepSpongeAbsorbInput x (fun i => x.prev (stSubSponge + i)) (fun i => x.prev (stWork + i))
  | .wotsTellFinalSqueeze => stepSqueezeInput x
  | .xmssMerkleBlockA =>
    stepMerkleBlockAGuards x domainMerkleNode (c0 +ₚ x.aux 1)
  | .xmssMerkleBlockB isLayerLast isTopFinal =>
    stepMerkleBlockBInput x ++
    (if !isLayerLast then []
     else if isTopFinal then
       [x.prev stCursorIdx] ++ (List.range 4).map (fun i => x.permOut i -ₚ x.pkRoot i)
     else
       [x.prev stCursorIdx] ++
       (List.range 4).map (fun i => stepBoolCheck (x.aux i)) ++
       (List.range 14).map (fun i => quarticBase4 (x.aux (4 + i))) ++
       (List.range 2).map (fun i => quarticBase4 (x.aux (18 + i))) ++
       (List.range 14).map (fun i => quarticBase4 (x.aux (20 + i))) ++
       [x.prev stTreeLo -ₚ
          (stepWeightedSum x.aux (fun i => 2 ^ i) 4 +ₚ
            (stepWeightedSum (fun i => x.aux (4 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›)),
        x.prev stTreeHi -ₚ
          (stepWeightedSum (fun i => x.aux (18 + i)) (fun i => 4 ^ i) 2 +ₚ
            (stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›))])

/-- Deterministic next-state limb `j` (`0 ≤ j < 44`) of one `StepConstraintKind` (never reads `x.next`). -/
def stepOpExpectedNext (kind : StepConstraintKind) (_c0 : Goldilocks) (x : StepOpRowInputs)
    (j : Nat) : Goldilocks :=
  match kind with
  | .idle => Goldilocks.zero
  | .statefulHmsgBlock0 =>
    if stepInBlock stCurRoot 4 j then x.pkRoot (j - stCurRoot)
    else if j = stKpIdx then stepWeightedSum x.aux (fun i => 2 ^ i) 6
    else if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge)
    else Goldilocks.zero
  | .statefulHmsgBlock1 | .forsRootsSpongeInit | .forsRootsPairAbsorb _
  | .detTreeHmsgBlock0 | .wotsTellInit | .wotsTellPairAbsorb _ =>
    if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge) else x.prev j
  | .statefulHmsgSqueeze | .detTreeHmsgBlock1 =>
    if stepInBlock stRemPack 6 j then Goldilocks.zero
    else if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge)
    else if j = stAccOrU1 then Goldilocks.zero
    else x.prev j
  | .statelessDeriveBlock0 =>
    if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge) else Goldilocks.zero
  | .statelessDeriveBlock1 =>
    if stepInBlock stMainSponge 12 j then x.permOut (j - stMainSponge)
    else if stepInBlock stRemPack 6 j then Goldilocks.zero
    else x.prev j
  | .statelessDecompLimb l => stepStatelessDecompExpected x l j
  | .forsLeafHash slot =>
    if j = stRemPack + slot then x.aux 8
    else if stepInBlock stWork 4 j then x.permOut (j - stWork) +ₚ x.aux (j - stWork)
    else if j = stCursorIdx then stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4
    else x.prev j
  | .forsMerkleBlockA | .xmssMerkleBlockA => stepMerkleBlockAExpectedNext x j
  | .forsMerkleBlockB isTreeLast isOddTree =>
    if isTreeLast && !isOddTree then
      if stepInBlock stCurRoot 4 j then x.permOut (j - stCurRoot) else x.prev j
    else
      if stepInBlock stWork 4 j then x.permOut (j - stWork) else x.prev j
  | .forsRootsFinalSqueeze =>
    if stepInBlock stCurRoot 4 j then x.permOut (j - stCurRoot) else x.prev j
  | .hmsgDecompLimb l => stepHmsgDecompExpected x l j
  | .wotsChainStep0 slot =>
    if j = stRemPack + slot then x.aux 7
    else if stepInBlock stWork 4 j then
      let i := j - stWork
      (x.aux 4 *ₚ x.aux i) +ₚ ((Goldilocks.one -ₚ x.aux 4) *ₚ (x.permOut i +ₚ x.aux i))
    else if j = stAccOrU1 then x.aux 5
    else if j = stWotsU2 then x.aux 6
    else x.prev j
  | .wotsChainStep1 =>
    if stepInBlock stWork 4 j then
      let i := j - stWork
      (x.prev stAccOrU1 *ₚ x.prev (stWork + i)) +ₚ
        ((Goldilocks.one -ₚ x.prev stAccOrU1) *ₚ (x.permOut i +ₚ x.prev (stWork + i)))
    else x.prev j
  | .wotsChainStep2 isOdd =>
    let base := if isOdd then stWork else stSubSponge
    if stepInBlock base 4 j then
      let i := j - base
      (x.prev stWotsU2 *ₚ x.prev (stWork + i)) +ₚ
        ((Goldilocks.one -ₚ x.prev stWotsU2) *ₚ (x.permOut i +ₚ x.prev (stWork + i)))
    else x.prev j
  | .wotsTellFinalSqueeze =>
    if stepInBlock stWork 4 j then x.permOut (j - stWork)
    else if j = stCursorIdx then x.prev stKpIdx
    else x.prev j
  | .xmssMerkleBlockB isLayerLast isTopFinal =>
    if !isLayerLast then
      if stepInBlock stWork 4 j then x.permOut (j - stWork) else x.prev j
    else if isTopFinal then
      Goldilocks.zero
    else
      if stepInBlock stCurRoot 4 j then x.permOut (j - stCurRoot)
      else if j = stKpIdx then stepWeightedSum x.aux (fun i => 2 ^ i) 4
      else if j = stTreeLo then
        stepWeightedSum (fun i => x.aux (4 + i)) (fun i => 4 ^ i) 14 +ₚ
          (stepWeightedSum (fun i => x.aux (18 + i)) (fun i => 4 ^ i) 2 *ₚ ‹2 ^ 28›)
      else if j = stTreeHi then
        stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14
      else x.prev j

theorem stepOpGuardResiduals_congr_next (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (next' : Nat → Goldilocks) :
    stepOpGuardResiduals kind c0 { x with next := next' } = stepOpGuardResiduals kind c0 x := by
  cases kind <;> rfl

theorem stepOpExpectedNext_congr_next (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (next' : Nat → Goldilocks) (j : Nat) :
    stepOpExpectedNext kind c0 { x with next := next' } j = stepOpExpectedNext kind c0 x j := by
  cases kind <;> rfl

private theorem allZero_map_iff (n : Nat) (f : Nat → Goldilocks) :
    allZeroGoldilocks ((List.range n).map f) = true ↔ ∀ i < n, f i = Goldilocks.zero := by
  unfold allZeroGoldilocks
  rw [List.all_map, List.all_eq_true]
  constructor
  · intro h i hi; exact beq_iff_eq.mp (h i (List.mem_range.mpr hi))
  · intro h i hi; exact beq_iff_eq.mpr (h i (List.mem_range.mp hi))

private theorem allZero_stepNextIsPerm_iff (x : StepOpRowInputs) (base n : Nat) :
    allZeroGoldilocks (stepNextIsPerm x base n) = true ↔
      ∀ i < n, x.next (base + i) = x.permOut i := by
  unfold stepNextIsPerm
  rw [allZero_map_iff]
  simp only [g_sub_eq_zero_iff]

private theorem allZero_filterMap_range_iff (n : Nat) (skip : Nat → Bool) (f : Nat → Goldilocks) :
    allZeroGoldilocks ((List.range n).filterMap (fun j => if skip j then none else some (f j))) = true ↔
      ∀ j < n, skip j = false → f j = Goldilocks.zero := by
  unfold allZeroGoldilocks
  rw [List.all_filterMap, List.all_eq_true]
  constructor
  · intro h j hj hSkip
    have hMem := h j (List.mem_range.mpr hj)
    simp only [hSkip, Bool.false_eq_true, ↓reduceIte, beq_iff_eq] at hMem
    exact hMem
  · intro h j hj
    cases hSkip : skip j
    · simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
      exact h j (List.mem_range.mp hj) hSkip
    · rfl

private theorem allZero_stepCarryUnchanged_iff (x : StepOpRowInputs) (changed : Nat → Bool) :
    allZeroGoldilocks (stepCarryUnchanged x changed) = true ↔
      ∀ j < 44, changed j = false → x.next j = x.prev j := by
  unfold stepCarryUnchanged
  rw [allZero_filterMap_range_iff]
  simp only [g_sub_eq_zero_iff]

private theorem allZero_stepZeroElsewhere_iff (x : StepOpRowInputs) (kept : Nat → Bool) :
    allZeroGoldilocks (stepZeroElsewhere x kept) = true ↔
      ∀ j < 44, kept j = false → x.next j = Goldilocks.zero := by
  unfold stepZeroElsewhere
  exact allZero_filterMap_range_iff 44 kept x.next

private theorem allZero_flatMap_triple_iff (n : Nat) (g1 g2 nRes : Nat → Goldilocks) :
    allZeroGoldilocks ((List.range n).flatMap (fun i => [g1 i, g2 i, nRes i])) = true ↔
      allZeroGoldilocks ((List.range n).flatMap (fun i => [g1 i, g2 i])) = true ∧
      ∀ i < n, nRes i = Goldilocks.zero := by
  unfold allZeroGoldilocks
  simp only [List.all_flatMap, List.all_cons, List.all_nil, Bool.and_true,
    List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    exact ⟨fun i hi => ⟨(h i hi).1, (h i hi).2.1⟩, fun i hi => (h i hi).2.2⟩
  · rintro ⟨hg, hn⟩ i hi
    exact ⟨(hg i hi).1, (hg i hi).2, hn i hi⟩

private theorem stepInBlock_iff (a n j : Nat) :
    stepInBlock a n j = true ↔ a ≤ j ∧ j < a + n := by
  unfold stepInBlock
  simp only [Bool.and_eq_true, decide_eq_true_eq]

private theorem stepMerkleBlockA_iff (x : StepOpRowInputs) (domainTag meta0 : Goldilocks) :
    allZeroGoldilocks (stepMerkleBlockA x domainTag meta0) = true ↔
      allZeroGoldilocks (stepMerkleBlockAGuards x domainTag meta0) = true ∧
      ∀ j < 44, x.next j = stepMerkleBlockAExpectedNext x j := by
  unfold stepMerkleBlockA stepMerkleBlockAGuards
  have hSingle : ∀ r : Goldilocks, allZeroGoldilocks [r] = (r == Goldilocks.zero) := by
    intro r; simp [allZeroGoldilocks]
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_flatMap_triple_iff,
    allZero_stepNextIsPerm_iff, hSingle, beq_iff_eq, g_sub_eq_zero_iff,
    allZero_stepCarryUnchanged_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨hG0, hG1, hNextWork⟩, hG2⟩, hNextSub⟩, hNextCur⟩, hCarry⟩
    refine ⟨⟨⟨hG0, hG1⟩, hG2⟩, fun j hj => ?_⟩
    unfold stepMerkleBlockAExpectedNext
    by_cases hSub : stepInBlock stSubSponge 12 j = true
    · rw [hSub]; simp only [↓reduceIte]
      obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stSubSponge 12 j).mp hSub
      have hi : j - stSubSponge < 12 := by unfold stSubSponge at *; omega
      have hAdd : stSubSponge + (j - stSubSponge) = j := by omega
      simpa only [hAdd] using hNextSub (j - stSubSponge) hi
    · have hSubF : stepInBlock stSubSponge 12 j = false := Bool.eq_false_iff.mpr hSub
      rw [hSubF]; simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hWk : stepInBlock stWork 4 j = true
      · rw [hWk]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hWk
        have hi : j - stWork < 4 := by unfold stWork at *; omega
        have hAdd : stWork + (j - stWork) = j := by omega
        simpa only [hAdd] using hNextWork (j - stWork) hi
      · have hWkF : stepInBlock stWork 4 j = false := Bool.eq_false_iff.mpr hWk
        rw [hWkF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hCur : j = stCursorIdx
        · subst hCur; simp [hNextCur]
        · simp only [hCur, ↓reduceIte]
          exact hCarry j hj (by simp [hSubF, hWkF, beq_false_of_ne hCur])
  · rintro ⟨⟨⟨hG0, hG1⟩, hG2⟩, hNext⟩
    refine ⟨⟨⟨⟨⟨hG0, hG1, fun i hi => ?_⟩, hG2⟩, fun i hi => ?_⟩, ?_⟩, fun j hj hCh => ?_⟩
    · rw [hNext (stWork + i) (by unfold stWork; omega)]
      unfold stepMerkleBlockAExpectedNext
      have hSubF : stepInBlock stSubSponge 12 (stWork + i) = false := by
        unfold stepInBlock stSubSponge stWork; simp
      have hWkT : stepInBlock stWork 4 (stWork + i) = true := by
        unfold stepInBlock stWork; simp; omega
      have hSubIdx : stWork + i - stWork = i := by omega
      simp [hSubF, hWkT, hSubIdx]
    · rw [hNext (stSubSponge + i) (by unfold stSubSponge; omega)]
      unfold stepMerkleBlockAExpectedNext
      have hSubT : stepInBlock stSubSponge 12 (stSubSponge + i) = true := by
        unfold stepInBlock stSubSponge; simp; omega
      have hSubIdx : stSubSponge + i - stSubSponge = i := by omega
      simp [hSubT, hSubIdx]
    · rw [hNext stCursorIdx (by decide)]
      unfold stepMerkleBlockAExpectedNext
      have hSubF : stepInBlock stSubSponge 12 stCursorIdx = false := by decide
      have hWkF : stepInBlock stWork 4 stCursorIdx = false := by decide
      simp [hSubF, hWkF]
    · rw [hNext j hj]
      unfold stepMerkleBlockAExpectedNext
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
      simp [hCh.1.1, hCh.1.2, hCh.2]

private theorem stepBlockUpdate_iff (x : StepOpRowInputs) (base n : Nat)
    (hEnd : base + n ≤ 44) :
    (allZeroGoldilocks (stepNextIsPerm x base n) = true ∧
     allZeroGoldilocks (stepCarryUnchanged x (fun j => stepInBlock base n j)) = true) ↔
      ∀ j < 44, x.next j = (if stepInBlock base n j then x.permOut (j - base) else x.prev j) := by
  rw [allZero_stepNextIsPerm_iff, allZero_stepCarryUnchanged_iff]
  constructor
  · rintro ⟨hPerm, hCarry⟩ j hj
    cases hIn : stepInBlock base n j
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hCarry j hj hIn
    · simp only [↓reduceIte]
      obtain ⟨hLo, hHi⟩ := (stepInBlock_iff base n j).mp hIn
      have hAdd : base + (j - base) = j := by omega
      simpa only [hAdd] using hPerm (j - base) (by omega)
  · intro hNext
    refine ⟨fun i hi => ?_, fun j hj hCh => ?_⟩
    · rw [hNext (base + i) (by omega)]
      have hIn : stepInBlock base n (base + i) = true :=
        (stepInBlock_iff base n (base + i)).mpr ⟨by omega, by omega⟩
      have hSub : base + i - base = i := by omega
      simp [hIn, hSub]
    · rw [hNext j hj, hCh]; rfl

/-- **Exact Guard + Functional Transition Decomposition (`stepOpConstraints_iff_guard_and_next`)**:
    For every valid `StepConstraintKind`, `stepOpConstraints kind c0 x` vanishes if and only if
    its pure pre-state guard list `stepOpGuardResiduals kind c0 x` vanishes AND all 44 `next`
    state limbs equal `stepOpExpectedNext kind c0 x j`. -/
theorem stepOpConstraints_iff_guard_and_next (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (hValid : kind.validSlot = true) :
    allZeroGoldilocks (stepOpConstraints kind c0 x) = true ↔
      allZeroGoldilocks (stepOpGuardResiduals kind c0 x) = true ∧
      ∀ j < 44, x.next j = stepOpExpectedNext kind c0 x j := by
  have hSingle : ∀ r : Goldilocks, allZeroGoldilocks [r] = (r == Goldilocks.zero) := by
    intro r; simp [allZeroGoldilocks]
  have hPair : ∀ r0 r1 : Goldilocks,
      allZeroGoldilocks [r0, r1] = ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero)) := by
    intros; simp [allZeroGoldilocks]
  cases kind with
  | idle =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    rw [allZero_map_iff]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  | statefulHmsgBlock0 =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    have hTail5 : ∀ (r0 r1 r2 r3 r4 : Goldilocks),
        allZeroGoldilocks [r0, r1, r2, r3, r4] =
          (allZeroGoldilocks [r0, r1, r2, r3] && (r4 == Goldilocks.zero)) := by
      intros; simp [allZeroGoldilocks, Bool.and_assoc]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_flatMap_triple_iff,
      hTail5, beq_iff_eq, g_sub_eq_zero_iff, allZero_stepNextIsPerm_iff,
      allZero_stepZeroElsewhere_iff]
    constructor
    · rintro ⟨⟨⟨⟨⟨hB6, hB32⟩, hStIn, hRoot⟩, hT4, hKp⟩, hMain⟩, hZero⟩
      refine ⟨⟨⟨⟨hB6, hB32⟩, hStIn⟩, hT4⟩, fun j hj => ?_⟩
      by_cases hC : stepInBlock stCurRoot 4 j = true
      · rw [hC]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stCurRoot 4 j).mp hC
        have hAdd : stCurRoot + (j - stCurRoot) = j := by unfold stCurRoot at *; omega
        simpa only [hAdd] using hRoot (j - stCurRoot) (by unfold stCurRoot at *; omega)
      · have hCF : stepInBlock stCurRoot 4 j = false := Bool.eq_false_iff.mpr hC
        rw [hCF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hK : j = stKpIdx
        · subst hK; simp [hKp]
        · simp only [hK, ↓reduceIte]
          by_cases hM : stepInBlock stMainSponge 12 j = true
          · rw [hM]; simp only [↓reduceIte]
            obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stMainSponge 12 j).mp hM
            have hAdd : stMainSponge + (j - stMainSponge) = j := by omega
            simpa only [hAdd] using hMain (j - stMainSponge) (by unfold stMainSponge at *; omega)
          · have hMF : stepInBlock stMainSponge 12 j = false := Bool.eq_false_iff.mpr hM
            rw [hMF]; simp only [Bool.false_eq_true, ↓reduceIte]
            exact hZero j hj (by simp [hCF, beq_false_of_ne hK, hMF])
    · rintro ⟨⟨⟨⟨hB6, hB32⟩, hStIn⟩, hT4⟩, hNext⟩
      refine ⟨⟨⟨⟨⟨hB6, hB32⟩, hStIn, fun i hi => ?_⟩, hT4, ?_⟩, fun i hi => ?_⟩, fun j hj hK => ?_⟩
      · rw [hNext (stCurRoot + i) (by unfold stCurRoot; omega)]
        have hC : stepInBlock stCurRoot 4 (stCurRoot + i) = true := by
          unfold stepInBlock stCurRoot; simp; omega
        have hSub : stCurRoot + i - stCurRoot = i := by omega
        simp [hC, hSub]
      · rw [hNext stKpIdx (by decide)]
        have hCF : stepInBlock stCurRoot 4 stKpIdx = false := by decide
        simp [hCF]
      · rw [hNext (stMainSponge + i) (by unfold stMainSponge; omega)]
        have hCF : stepInBlock stCurRoot 4 (stMainSponge + i) = false := by
          unfold stepInBlock stCurRoot stMainSponge; simp; omega
        have hKNe : stMainSponge + i ≠ stKpIdx := by unfold stMainSponge stKpIdx; omega
        have hMT : stepInBlock stMainSponge 12 (stMainSponge + i) = true := by
          unfold stepInBlock stMainSponge; simp; omega
        have hSub : stMainSponge + i - stMainSponge = i := by omega
        simp [hCF, hKNe, hMT, hSub]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hK
        simp [hK.1.1, hK.1.2, hK.2]
  | statefulHmsgBlock1 | forsRootsSpongeInit | forsRootsPairAbsorb _
  | detTreeHmsgBlock0 | wotsTellInit | wotsTellPairAbsorb _ =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    simp only [allZeroGoldilocks_append, Bool.and_eq_true]
    rw [and_assoc]
    exact and_congr_right' (stepBlockUpdate_iff x stMainSponge 12 (by decide))
  | statefulHmsgSqueeze | detTreeHmsgBlock1 =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_stepNextIsPerm_iff,
      allZero_map_iff, hSingle, beq_iff_eq, allZero_stepCarryUnchanged_iff]
    rw [and_assoc, and_assoc, and_assoc]
    apply and_congr_right'
    constructor
    · rintro ⟨hMain, hRem, hAcc, hCarry⟩ j hj
      by_cases hR : stepInBlock stRemPack 6 j = true
      · rw [hR]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stRemPack 6 j).mp hR
        have hAdd : stRemPack + (j - stRemPack) = j := by omega
        simpa only [hAdd] using hRem (j - stRemPack) (by unfold stRemPack at *; omega)
      · have hRF : stepInBlock stRemPack 6 j = false := Bool.eq_false_iff.mpr hR
        rw [hRF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hM : stepInBlock stMainSponge 12 j = true
        · rw [hM]; simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stMainSponge 12 j).mp hM
          have hAdd : stMainSponge + (j - stMainSponge) = j := by omega
          simpa only [hAdd] using hMain (j - stMainSponge) (by unfold stMainSponge at *; omega)
        · have hMF : stepInBlock stMainSponge 12 j = false := Bool.eq_false_iff.mpr hM
          rw [hMF]; simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hA : j = stAccOrU1
          · subst hA; simp [hAcc]
          · simp only [hA, ↓reduceIte]
            exact hCarry j hj (by simp [hRF, hMF, beq_false_of_ne hA])
    · intro hNext
      refine ⟨fun i hi => ?_, fun s hs => ?_, ?_, fun j hj hCh => ?_⟩
      · rw [hNext (stMainSponge + i) (by unfold stMainSponge; omega)]
        have hRF : stepInBlock stRemPack 6 (stMainSponge + i) = false := by
          unfold stepInBlock stRemPack stMainSponge; simp
        have hMT : stepInBlock stMainSponge 12 (stMainSponge + i) = true := by
          unfold stepInBlock stMainSponge; simp; omega
        have hSub : stMainSponge + i - stMainSponge = i := by omega
        simp [hRF, hMT, hSub]
      · rw [hNext (stRemPack + s) (by unfold stRemPack; omega)]
        have hRT : stepInBlock stRemPack 6 (stRemPack + s) = true := by
          unfold stepInBlock stRemPack; simp; omega
        simp [hRT]
      · rw [hNext stAccOrU1 (by decide)]
        have hRF : stepInBlock stRemPack 6 stAccOrU1 = false := by decide
        have hMF : stepInBlock stMainSponge 12 stAccOrU1 = false := by decide
        simp [hRF, hMF]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
        simp [hCh.1.1, hCh.1.2, hCh.2]
  | statelessDeriveBlock0 =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_stepNextIsPerm_iff,
      allZero_stepZeroElsewhere_iff]
    rw [and_assoc]
    apply and_congr_right'
    constructor
    · rintro ⟨hMain, hZero⟩ j hj
      cases hM : stepInBlock stMainSponge 12 j
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hZero j hj hM
      · simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stMainSponge 12 j).mp hM
        have hAdd : stMainSponge + (j - stMainSponge) = j := by omega
        simpa only [hAdd] using hMain (j - stMainSponge) (by unfold stMainSponge at *; omega)
    · intro hNext
      refine ⟨fun i hi => ?_, fun j hj hM => ?_⟩
      · rw [hNext (stMainSponge + i) (by unfold stMainSponge; omega)]
        have hMT : stepInBlock stMainSponge 12 (stMainSponge + i) = true := by
          unfold stepInBlock stMainSponge; simp; omega
        have hSub : stMainSponge + i - stMainSponge = i := by omega
        simp [hMT, hSub]
      · rw [hNext j hj, hM]; rfl
  | statelessDeriveBlock1 =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_stepNextIsPerm_iff,
      allZero_map_iff, allZero_stepCarryUnchanged_iff]
    rw [and_assoc, and_assoc]
    apply and_congr_right'
    constructor
    · rintro ⟨hMain, hRem, hCarry⟩ j hj
      by_cases hM : stepInBlock stMainSponge 12 j = true
      · rw [hM]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stMainSponge 12 j).mp hM
        have hAdd : stMainSponge + (j - stMainSponge) = j := by omega
        simpa only [hAdd] using hMain (j - stMainSponge) (by unfold stMainSponge at *; omega)
      · have hMF : stepInBlock stMainSponge 12 j = false := Bool.eq_false_iff.mpr hM
        rw [hMF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hR : stepInBlock stRemPack 6 j = true
        · rw [hR]; simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stRemPack 6 j).mp hR
          have hAdd : stRemPack + (j - stRemPack) = j := by omega
          simpa only [hAdd] using hRem (j - stRemPack) (by unfold stRemPack at *; omega)
        · have hRF : stepInBlock stRemPack 6 j = false := Bool.eq_false_iff.mpr hR
          rw [hRF]; simp only [Bool.false_eq_true, ↓reduceIte]
          exact hCarry j hj (by simp [hMF, hRF])
    · intro hNext
      refine ⟨fun i hi => ?_, fun s hs => ?_, fun j hj hCh => ?_⟩
      · rw [hNext (stMainSponge + i) (by unfold stMainSponge; omega)]
        have hMT : stepInBlock stMainSponge 12 (stMainSponge + i) = true := by
          unfold stepInBlock stMainSponge; simp; omega
        have hSub : stMainSponge + i - stMainSponge = i := by omega
        simp [hMT, hSub]
      · rw [hNext (stRemPack + s) (by unfold stRemPack; omega)]
        have hMF : stepInBlock stMainSponge 12 (stRemPack + s) = false := by
          unfold stepInBlock stRemPack stMainSponge; simp; omega
        have hRT : stepInBlock stRemPack 6 (stRemPack + s) = true := by
          unfold stepInBlock stRemPack; simp; omega
        simp [hMF, hRT]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff] at hCh
        simp [hCh.1, hCh.2]
  | statelessDecompLimb l =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_map_iff, g_sub_eq_zero_iff]
  | forsLeafHash slot =>
    have hSlotLt : slot < 6 := by simpa [StepConstraintKind.validSlot] using hValid
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    have hTail5 : ∀ (r0 r1 r2 r3 r4 : Goldilocks),
        allZeroGoldilocks [r0, r1, r2, r3, r4] =
          (allZeroGoldilocks [r0, r1, r2, r3] && (r4 == Goldilocks.zero)) := by
      intros; simp [allZeroGoldilocks, Bool.and_assoc]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, hSingle, hPair, hTail5,
      allZero_flatMap_triple_iff, beq_iff_eq, g_sub_eq_zero_iff,
      allZero_stepCarryUnchanged_iff]
    constructor
    · rintro ⟨⟨⟨⟨hQ, hPack, hNextPack⟩, hIn, hNextWk⟩, hT4, hNextCur⟩, hCarry⟩
      refine ⟨⟨⟨⟨hQ, hPack⟩, hIn⟩, hT4⟩, fun j hj => ?_⟩
      by_cases hP : j = stRemPack + slot
      · subst hP; simp [hNextPack]
      · simp only [hP, ↓reduceIte]
        by_cases hW : stepInBlock stWork 4 j = true
        · rw [hW]; simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hW
          have hAdd : stWork + (j - stWork) = j := by omega
          simpa only [hAdd] using hNextWk (j - stWork) (by unfold stWork at *; omega)
        · have hWF : stepInBlock stWork 4 j = false := Bool.eq_false_iff.mpr hW
          rw [hWF]; simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hC : j = stCursorIdx
          · subst hC; simp [hNextCur]
          · simp only [hC, ↓reduceIte]
            exact hCarry j hj (by simp [beq_false_of_ne hP, hWF, beq_false_of_ne hC])
    · rintro ⟨⟨⟨⟨hQ, hPack⟩, hIn⟩, hT4⟩, hNext⟩
      refine ⟨⟨⟨⟨hQ, hPack, ?_⟩, hIn, fun i hi => ?_⟩, hT4, ?_⟩, fun j hj hCh => ?_⟩
      · rw [hNext (stRemPack + slot) (by unfold stRemPack; omega)]; simp
      · rw [hNext (stWork + i) (by unfold stWork; omega)]
        have hPNe : stWork + i ≠ stRemPack + slot := by unfold stWork stRemPack; omega
        have hWT : stepInBlock stWork 4 (stWork + i) = true := by
          unfold stepInBlock stWork; simp; omega
        have hSub : stWork + i - stWork = i := by omega
        simp [hPNe, hWT, hSub]
      · rw [hNext stCursorIdx (by decide)]
        have hPNe : stCursorIdx ≠ stRemPack + slot := by unfold stCursorIdx stRemPack; omega
        have hWF : stepInBlock stWork 4 stCursorIdx = false := by decide
        simp [hPNe, hWF]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
        simp [hCh.1.1, hCh.1.2, hCh.2]
  | forsMerkleBlockA =>
    exact stepMerkleBlockA_iff x domainForsNode ((c0 +ₚ (x.prev stKpIdx *ₚ ‹2 ^ 16›)) +ₚ x.aux 1)
  | forsMerkleBlockB isTreeLast isOddTree =>
    cases isTreeLast <;> cases isOddTree
    · unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
      simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte, List.append_nil,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stWork 4 (by decide))
    · unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
      simp only [Bool.false_eq_true, Bool.false_and, ↓reduceIte, List.append_nil,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stWork 4 (by decide))
    · have hSplit :
          stepOpConstraints (.forsMerkleBlockB true false) c0 x =
            stepOpGuardResiduals (.forsMerkleBlockB true false) c0 x ++
            (stepNextIsPerm x stCurRoot 4 ++
             stepCarryUnchanged x (fun j => stepInBlock stCurRoot 4 j)) := by
        simp only [stepOpConstraints, stepOpGuardResiduals,
          Bool.not_false, Bool.and_self, ↓reduceIte, List.append_assoc]
      rw [hSplit, allZeroGoldilocks_append, Bool.and_eq_true]
      unfold stepOpExpectedNext
      simp only [Bool.not_false, Bool.and_self, ↓reduceIte,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stCurRoot 4 (by decide))
    · have hSplit :
          stepOpConstraints (.forsMerkleBlockB true true) c0 x =
            stepOpGuardResiduals (.forsMerkleBlockB true true) c0 x ++
            (stepNextIsPerm x stWork 4 ++
             stepCarryUnchanged x (fun j => stepInBlock stWork 4 j)) := by
        simp only [stepOpConstraints, stepOpGuardResiduals,
          Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
      rw [hSplit, allZeroGoldilocks_append, Bool.and_eq_true]
      unfold stepOpExpectedNext
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stWork 4 (by decide))
  | forsRootsFinalSqueeze =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    simp only [allZeroGoldilocks_append, Bool.and_eq_true]
    rw [and_assoc]
    exact and_congr_right' (stepBlockUpdate_iff x stCurRoot 4 (by decide))
  | hmsgDecompLimb l =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_map_iff, g_sub_eq_zero_iff]
  | wotsChainStep0 slot =>
    have hSlotLt : slot < 5 := by simpa [StepConstraintKind.validSlot] using hValid
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    have hHead7 : ∀ (r0 r1 r2 r3 r4 r5 r6 : Goldilocks),
        allZeroGoldilocks [r0, r1, r2, r3, r4, r5, r6] =
          (allZeroGoldilocks [r0, r1, r2, r3, r4, r5] && (r6 == Goldilocks.zero)) := by
      intros; simp [allZeroGoldilocks, Bool.and_assoc]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, hHead7, hPair,
      allZero_flatMap_triple_iff, beq_iff_eq, g_sub_eq_zero_iff,
      allZero_stepCarryUnchanged_iff]
    constructor
    · rintro ⟨⟨⟨⟨⟨hU, hNextPack⟩, hIn, hNextWk⟩, hStepIn⟩, hNextU1, hNextU2⟩, hCarry⟩
      refine ⟨⟨⟨hU, hIn⟩, hStepIn⟩, fun j hj => ?_⟩
      by_cases hP : j = stRemPack + slot
      · subst hP; simp [hNextPack]
      · simp only [hP, ↓reduceIte]
        by_cases hW : stepInBlock stWork 4 j = true
        · rw [hW]; simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hW
          have hAdd : stWork + (j - stWork) = j := by omega
          simpa only [hAdd] using hNextWk (j - stWork) (by unfold stWork at *; omega)
        · have hWF : stepInBlock stWork 4 j = false := Bool.eq_false_iff.mpr hW
          rw [hWF]; simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hU1 : j = stAccOrU1
          · subst hU1; simp [hNextU1]
          · simp only [hU1, ↓reduceIte]
            by_cases hU2 : j = stWotsU2
            · subst hU2; simp [hNextU2]
            · simp only [hU2, ↓reduceIte]
              exact hCarry j hj
                (by simp [beq_false_of_ne hP, hWF, beq_false_of_ne hU1, beq_false_of_ne hU2])
    · rintro ⟨⟨⟨hU, hIn⟩, hStepIn⟩, hNext⟩
      refine ⟨⟨⟨⟨⟨hU, ?_⟩, hIn, fun i hi => ?_⟩, hStepIn⟩, ?_, ?_⟩, fun j hj hCh => ?_⟩
      · rw [hNext (stRemPack + slot) (by unfold stRemPack; omega)]; simp
      · rw [hNext (stWork + i) (by unfold stWork; omega)]
        have hPNe : stWork + i ≠ stRemPack + slot := by unfold stWork stRemPack; omega
        have hWT : stepInBlock stWork 4 (stWork + i) = true := by
          unfold stepInBlock stWork; simp; omega
        have hSub : stWork + i - stWork = i := by omega
        simp [hPNe, hWT, hSub]
      · rw [hNext stAccOrU1 (by decide)]
        have hPNe : stAccOrU1 ≠ stRemPack + slot := by unfold stAccOrU1 stRemPack; omega
        have hWF : stepInBlock stWork 4 stAccOrU1 = false := by decide
        simp [hPNe, hWF]
      · rw [hNext stWotsU2 (by decide)]
        have hPNe : stWotsU2 ≠ stRemPack + slot := by unfold stWotsU2 stRemPack; omega
        have hWF : stepInBlock stWork 4 stWotsU2 = false := by decide
        have hU1Ne : stWotsU2 ≠ stAccOrU1 := by decide
        simp [hPNe, hWF, hU1Ne]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
        simp [hCh.1.1.1, hCh.1.1.2, hCh.1.2, hCh.2]
  | wotsChainStep1 =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_flatMap_triple_iff,
      g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
    constructor
    · rintro ⟨⟨⟨hIn, hNextWk⟩, hStepIn⟩, hCarry⟩
      refine ⟨⟨hIn, hStepIn⟩, fun j hj => ?_⟩
      cases hW : stepInBlock stWork 4 j
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hCarry j hj hW
      · simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hW
        have hAdd : stWork + (j - stWork) = j := by omega
        simpa only [hAdd] using hNextWk (j - stWork) (by unfold stWork at *; omega)
    · rintro ⟨⟨hIn, hStepIn⟩, hNext⟩
      refine ⟨⟨⟨hIn, fun i hi => ?_⟩, hStepIn⟩, fun j hj hCh => ?_⟩
      · rw [hNext (stWork + i) (by unfold stWork; omega)]
        have hWT : stepInBlock stWork 4 (stWork + i) = true := by
          unfold stepInBlock stWork; simp; omega
        have hSub : stWork + i - stWork = i := by omega
        simp [hWT, hSub]
      · rw [hNext j hj, hCh]; rfl
  | wotsChainStep2 isOdd =>
    cases isOdd
    · unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
      simp only [Bool.false_eq_true, ↓reduceIte, allZeroGoldilocks_append, Bool.and_eq_true,
        allZero_flatMap_triple_iff, g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
      constructor
      · rintro ⟨⟨⟨hIn, hNextB⟩, hStepIn⟩, hCarry⟩
        refine ⟨⟨hIn, hStepIn⟩, fun j hj => ?_⟩
        cases hB : stepInBlock stSubSponge 4 j
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact hCarry j hj hB
        · simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stSubSponge 4 j).mp hB
          have hAdd : stSubSponge + (j - stSubSponge) = j := by omega
          simpa only [hAdd] using hNextB (j - stSubSponge) (by unfold stSubSponge at *; omega)
      · rintro ⟨⟨hIn, hStepIn⟩, hNext⟩
        refine ⟨⟨⟨hIn, fun i hi => ?_⟩, hStepIn⟩, fun j hj hCh => ?_⟩
        · rw [hNext (stSubSponge + i) (by unfold stSubSponge; omega)]
          have hBT : stepInBlock stSubSponge 4 (stSubSponge + i) = true := by
            unfold stepInBlock stSubSponge; simp; omega
          have hSub : stSubSponge + i - stSubSponge = i := by omega
          simp [hBT, hSub]
        · rw [hNext j hj, hCh]; rfl
    · unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
      simp only [↓reduceIte, allZeroGoldilocks_append, Bool.and_eq_true,
        allZero_flatMap_triple_iff, g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
      constructor
      · rintro ⟨⟨⟨hIn, hNextB⟩, hStepIn⟩, hCarry⟩
        refine ⟨⟨hIn, hStepIn⟩, fun j hj => ?_⟩
        cases hB : stepInBlock stWork 4 j
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact hCarry j hj hB
        · simp only [↓reduceIte]
          obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hB
          have hAdd : stWork + (j - stWork) = j := by omega
          simpa only [hAdd] using hNextB (j - stWork) (by unfold stWork at *; omega)
      · rintro ⟨⟨hIn, hStepIn⟩, hNext⟩
        refine ⟨⟨⟨hIn, fun i hi => ?_⟩, hStepIn⟩, fun j hj hCh => ?_⟩
        · rw [hNext (stWork + i) (by unfold stWork; omega)]
          have hBT : stepInBlock stWork 4 (stWork + i) = true := by
            unfold stepInBlock stWork; simp; omega
          have hSub : stWork + i - stWork = i := by omega
          simp [hBT, hSub]
        · rw [hNext j hj, hCh]; rfl
  | wotsTellFinalSqueeze =>
    unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, allZero_stepNextIsPerm_iff,
      hSingle, beq_iff_eq, g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
    rw [and_assoc, and_assoc]
    apply and_congr_right'
    constructor
    · rintro ⟨hWk, hCur, hCarry⟩ j hj
      by_cases hW : stepInBlock stWork 4 j = true
      · rw [hW]; simp only [↓reduceIte]
        obtain ⟨hLo, hHi⟩ := (stepInBlock_iff stWork 4 j).mp hW
        have hAdd : stWork + (j - stWork) = j := by omega
        simpa only [hAdd] using hWk (j - stWork) (by unfold stWork at *; omega)
      · have hWF : stepInBlock stWork 4 j = false := Bool.eq_false_iff.mpr hW
        rw [hWF]; simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hC : j = stCursorIdx
        · subst hC; simp [hCur]
        · simp only [hC, ↓reduceIte]
          exact hCarry j hj (by simp [hWF, beq_false_of_ne hC])
    · intro hNext
      refine ⟨fun i hi => ?_, ?_, fun j hj hCh => ?_⟩
      · rw [hNext (stWork + i) (by unfold stWork; omega)]
        have hWT : stepInBlock stWork 4 (stWork + i) = true := by
          unfold stepInBlock stWork; simp; omega
        have hSub : stWork + i - stWork = i := by omega
        simp [hWT, hSub]
      · rw [hNext stCursorIdx (by decide)]
        have hWF : stepInBlock stWork 4 stCursorIdx = false := by decide
        simp [hWF]
      · rw [hNext j hj]
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
        simp [hCh.1, hCh.2]
  | xmssMerkleBlockA =>
    exact stepMerkleBlockA_iff x domainMerkleNode (c0 +ₚ x.aux 1)
  | xmssMerkleBlockB isLayerLast isTopFinal =>
    cases isLayerLast
    · unfold stepOpConstraints stepOpGuardResiduals stepOpExpectedNext
      simp only [Bool.not_false, ↓reduceIte, List.append_nil,
        allZeroGoldilocks_append, Bool.and_eq_true]
      exact and_congr_right' (stepBlockUpdate_iff x stWork 4 (by decide))
    · cases isTopFinal
      · -- `isLayerLast = true, isTopFinal = false`
        have hSplitList :
            stepOpConstraints (.xmssMerkleBlockB true false) c0 x =
              stepOpGuardResiduals (.xmssMerkleBlockB true false) c0 x ++
              (stepNextIsPerm x stCurRoot 4 ++
               [x.next stKpIdx -ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 4,
                x.next stTreeLo -ₚ
                  (stepWeightedSum (fun i => x.aux (4 + i)) (fun i => 4 ^ i) 14 +ₚ
                    (stepWeightedSum (fun i => x.aux (18 + i)) (fun i => 4 ^ i) 2 *ₚ ‹2 ^ 28›)),
                x.next stTreeHi -ₚ stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14] ++
               stepCarryUnchanged x
                 (fun j => stepInBlock stCurRoot 4 j || j == stKpIdx || j == stTreeLo || j == stTreeHi)) := by
          simp only [stepOpConstraints, stepOpGuardResiduals,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
        rw [hSplitList, allZeroGoldilocks_append, Bool.and_eq_true]
        apply and_congr_right'
        unfold stepOpExpectedNext
        have hTriple : ∀ (r0 r1 r2 : Goldilocks),
            allZeroGoldilocks [r0, r1, r2] =
              ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero) && (r2 == Goldilocks.zero)) := by
          intros; simp [allZeroGoldilocks, Bool.and_assoc]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, allZeroGoldilocks_append,
          Bool.and_eq_true, allZero_stepNextIsPerm_iff, hTriple, beq_iff_eq,
          g_sub_eq_zero_iff, allZero_stepCarryUnchanged_iff]
        constructor
        · rintro ⟨⟨hCur, ⟨hKp, hLo⟩, hHi⟩, hCarry⟩ j hj
          by_cases hC : stepInBlock stCurRoot 4 j = true
          · rw [hC]; simp only [↓reduceIte]
            obtain ⟨hLoB, hHiB⟩ := (stepInBlock_iff stCurRoot 4 j).mp hC
            have hAdd : stCurRoot + (j - stCurRoot) = j := by omega
            simpa only [hAdd] using hCur (j - stCurRoot) (by unfold stCurRoot at *; omega)
          · have hCF : stepInBlock stCurRoot 4 j = false := Bool.eq_false_iff.mpr hC
            rw [hCF]; simp only [Bool.false_eq_true, ↓reduceIte]
            by_cases hK : j = stKpIdx
            · subst hK; simp [hKp]
            · simp only [hK, ↓reduceIte]
              by_cases hTL : j = stTreeLo
              · subst hTL; simp [hLo]
              · simp only [hTL, ↓reduceIte]
                by_cases hTH : j = stTreeHi
                · subst hTH; simp [hHi]
                · simp only [hTH, ↓reduceIte]
                  exact hCarry j hj
                    (by simp [hCF, beq_false_of_ne hK, beq_false_of_ne hTL, beq_false_of_ne hTH])
        · intro hNext
          refine ⟨⟨fun i hi => ?_, ⟨?_, ?_⟩, ?_⟩, fun j hj hCh => ?_⟩
          · rw [hNext (stCurRoot + i) (by unfold stCurRoot; omega)]
            have hCT : stepInBlock stCurRoot 4 (stCurRoot + i) = true := by
              unfold stepInBlock stCurRoot; simp; omega
            have hSub : stCurRoot + i - stCurRoot = i := by omega
            simp [hCT, hSub]
          · rw [hNext stKpIdx (by decide)]
            have hCF : stepInBlock stCurRoot 4 stKpIdx = false := by decide
            simp [hCF]
          · rw [hNext stTreeLo (by decide)]
            have hCF : stepInBlock stCurRoot 4 stTreeLo = false := by decide
            have hKNe : stTreeLo ≠ stKpIdx := by decide
            simp [hCF, hKNe]
          · rw [hNext stTreeHi (by decide)]
            have hCF : stepInBlock stCurRoot 4 stTreeHi = false := by decide
            have hKNe : stTreeHi ≠ stKpIdx := by decide
            have hTLNe : stTreeHi ≠ stTreeLo := by decide
            simp [hCF, hKNe, hTLNe]
          · rw [hNext j hj]
            simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hCh
            simp [hCh.1.1.1, hCh.1.1.2, hCh.1.2, hCh.2]
      · -- `isLayerLast = true, isTopFinal = true`
        have hSplitList :
            stepOpConstraints (.xmssMerkleBlockB true true) c0 x =
              stepOpGuardResiduals (.xmssMerkleBlockB true true) c0 x ++
              (List.range 44).map x.next := by
          simp only [stepOpConstraints, stepOpGuardResiduals,
            Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
        rw [hSplitList, allZeroGoldilocks_append, Bool.and_eq_true]
        apply and_congr_right'
        unfold stepOpExpectedNext
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, allZero_map_iff]

/-- Selector-explicit 256-column `Hem` AIR row: pairs a `StepOpRow` (`256` witness columns)
    with explicit field-valued `StepOp` selectors `sels` (`52` selectors over `allStepConstraintKinds`). -/
structure HemStepOpSelectorRow where
  row  : StepOpRow
  sels : List Goldilocks
  deriving DecidableEq, Repr

/-- Index of a `StepConstraintKind` inside `allStepConstraintKinds`. -/
def stepConstraintKindIdx (kind : StepConstraintKind) : Nat :=
  allStepConstraintKinds.idxOf kind

/-- Canonical one-hot selector vector for `kind` over `allStepConstraintKinds`. -/
def oneHotStepSelectors (kind : StepConstraintKind) : List Goldilocks :=
  allStepConstraintKinds.map fun k => if k == kind then Goldilocks.one else Goldilocks.zero

/-- Selector booleanity residuals `s_k * (1 - s_k)` for all `k < allStepConstraintKinds.length`. -/
def hemStepSelectorBoolResiduals (sels : List Goldilocks) : List Goldilocks :=
  (List.range allStepConstraintKinds.length).map fun k =>
    stepBoolCheck (sels.getD k Goldilocks.zero)

/-- Selector pairwise-orthogonality residuals `s_i * s_j` for all `0 ≤ i < j < allStepConstraintKinds.length`. -/
def hemStepSelectorOrthResiduals (sels : List Goldilocks) : List Goldilocks :=
  (List.range allStepConstraintKinds.length).flatMap fun i =>
    (List.range i).map fun j =>
      sels.getD j Goldilocks.zero *ₚ sels.getD i Goldilocks.zero

/-- Scheduled opcode pin residuals:
    - On an inactive slot (`none`), every selector is pinned to `0`.
    - On an active slot (`some _`), the scheduled selector `s_{uid_t}` is pinned to `1`. -/
def hemStepSchedulePinResiduals (profile : AggSigProfile) (slot : StepOpSlot) (t : Nat)
    (sels : List Goldilocks) : List Goldilocks :=
  match slot with
  | none =>
    (List.range allStepConstraintKinds.length).map fun k => sels.getD k Goldilocks.zero
  | some _ =>
    let kind := (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1
    [Goldilocks.one -ₚ sels.getD (stepConstraintKindIdx kind) Goldilocks.zero]

/-- Selector-muxed opcode guard & next-state transition residuals on row `t`:
    - Each `kind_k`'s pure pre-state guard list is gated by `s_k * g = 0`.
    - On an active slot, each `next` limb satisfies `x.next j = Σ_k s_k * stepOpExpectedNext kind_k c0 x j`. -/
def hemStepMuxedInputResiduals (c0 : Goldilocks) (x : StepOpRowInputs)
    (sels : List Goldilocks) : List Goldilocks :=
  let guardRes :=
    (List.range allStepConstraintKinds.length).flatMap fun k =>
      let sk := sels.getD k Goldilocks.zero
      let kind := allStepConstraintKinds.getD k .idle
      (stepOpGuardResiduals kind c0 x).map (fun g => sk *ₚ g)
  let nextRes :=
    (List.range 44).map fun j =>
      x.next j -ₚ
        (List.range allStepConstraintKinds.length).foldl
          (fun acc k =>
            acc +ₚ (sels.getD k Goldilocks.zero *ₚ
              stepOpExpectedNext (allStepConstraintKinds.getD k .idle) c0 x j))
          Goldilocks.zero
  guardRes ++ nextRes

/-- Read the shared mux evaluator's inputs from the committed row. -/
def hemStepMuxedOpResiduals (slot : StepOpSlot) (c0 : Goldilocks) (row : StepOpRow)
    (sels : List Goldilocks) : List Goldilocks :=
  match slot with
  | none => []
  | some pub => hemStepMuxedInputResiduals c0 (stepOpRowInputs pub row) sels

/-- Full intra-row residuals of a selector-explicit `HemStepOpSelectorRow` (including `s_i * s_j = 0`). -/
def hemStepSelectorRowResiduals (profile : AggSigProfile) (slot : StepOpSlot) (t : Nat)
    (sr : HemStepOpSelectorRow) : List Goldilocks :=
  let c0 := Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).2
  (stepOpPermTrace sr.row).2 ++
  stepOpBoundaryResiduals (stepOpRowsPerSigner profile) t sr.row ++
  hemStepSelectorBoolResiduals sr.sels ++
  hemStepSelectorOrthResiduals sr.sels ++
  hemStepSchedulePinResiduals profile slot t sr.sels ++
  hemStepMuxedOpResiduals slot c0 sr.row sr.sels

/-- Mutated intra-row residuals omitting ONLY pairwise selector orthogonality `s_i * s_j = 0` (for `#tooth`). -/
def hemStepSelectorRowResidualsOmitOrthogonality (profile : AggSigProfile) (slot : StepOpSlot)
    (t : Nat) (sr : HemStepOpSelectorRow) : List Goldilocks :=
  let c0 := Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).2
  (stepOpPermTrace sr.row).2 ++
  stepOpBoundaryResiduals (stepOpRowsPerSigner profile) t sr.row ++
  hemStepSelectorBoolResiduals sr.sels ++
  hemStepSchedulePinResiduals profile slot t sr.sels ++
  hemStepMuxedOpResiduals slot c0 sr.row sr.sels

def hemStepSelectorIntraFrom (profile : AggSigProfile) (slots : List StepOpSlot) :
    Nat → List HemStepOpSelectorRow → List Goldilocks
  | _, [] => []
  | g, sr :: rest =>
    hemStepSelectorRowResiduals profile (slots.getD (g / stepOpRowsPerSigner profile) none)
      (g % stepOpRowsPerSigner profile) sr ++
    hemStepSelectorIntraFrom profile slots (g + 1) rest

def hemStepSelectorIntraOmitOrthFrom (profile : AggSigProfile) (slots : List StepOpSlot) :
    Nat → List HemStepOpSelectorRow → List Goldilocks
  | _, [] => []
  | g, sr :: rest =>
    hemStepSelectorRowResidualsOmitOrthogonality profile
      (slots.getD (g / stepOpRowsPerSigner profile) none)
      (g % stepOpRowsPerSigner profile) sr ++
    hemStepSelectorIntraOmitOrthFrom profile slots (g + 1) rest

/-- Full selector-explicit 256-column `Hem` AIR validity predicate. -/
def hemStepTraceValid (profile : AggSigProfile) (slots : List StepOpSlot)
    (srows : List HemStepOpSelectorRow) : Bool :=
  decide (0 < slots.length) &&
  decide (srows.length = slots.length * stepOpRowsPerSigner profile) &&
  srows.all (fun sr => sr.row.wellShaped && decide (sr.sels.length = allStepConstraintKinds.length)) &&
  allZeroGoldilocks (hemStepSelectorIntraFrom profile slots 0 srows) &&
  allZeroGoldilocks (stepOp256ShiftResiduals (srows.map HemStepOpSelectorRow.row))

/-- Mutated selector-explicit 256-column `Hem` AIR validity predicate omitting ONLY `s_i * s_j = 0`. -/
def hemStepTraceValidOmitOrthogonality (profile : AggSigProfile) (slots : List StepOpSlot)
    (srows : List HemStepOpSelectorRow) : Bool :=
  decide (0 < slots.length) &&
  decide (srows.length = slots.length * stepOpRowsPerSigner profile) &&
  srows.all (fun sr => sr.row.wellShaped && decide (sr.sels.length = allStepConstraintKinds.length)) &&
  allZeroGoldilocks (hemStepSelectorIntraOmitOrthFrom profile slots 0 srows) &&
  allZeroGoldilocks (stepOp256ShiftResiduals (srows.map HemStepOpSelectorRow.row))

/-- Attach canonical scheduled selectors to a `StepOpRow` table. -/
def attachHonestStepSelectorsFrom (profile : AggSigProfile) (slots : List StepOpSlot) :
    Nat → List StepOpRow → List HemStepOpSelectorRow
  | _, [] => []
  | g, row :: rest =>
    let slot := slots.getD (g / stepOpRowsPerSigner profile) none
    let t := g % stepOpRowsPerSigner profile
    let sels := match slot with
      | none => List.replicate allStepConstraintKinds.length Goldilocks.zero
      | some _ =>
        oneHotStepSelectors (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1
    { row := row, sels := sels } :: attachHonestStepSelectorsFrom profile slots (g + 1) rest

def attachHonestStepSelectors (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) : List HemStepOpSelectorRow :=
  attachHonestStepSelectorsFrom profile slots 0 rows

private theorem allZero_orth_iff (sels : List Goldilocks) :
    allZeroGoldilocks (hemStepSelectorOrthResiduals sels) = true ↔
      ∀ i j, j < i → i < allStepConstraintKinds.length →
        sels.getD j Goldilocks.zero *ₚ sels.getD i Goldilocks.zero = Goldilocks.zero := by
  unfold hemStepSelectorOrthResiduals allZeroGoldilocks
  simp only [List.all_flatMap, List.all_map, List.all_eq_true, List.mem_range,
    Function.comp_apply, beq_iff_eq]
  exact ⟨fun h i j hji hi => h i hi j hji, fun h i hi j hji => h i j hji hi⟩

private theorem nodup_getElem_inj {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      xs[i]'hi = xs[j]'hj → i = j
  | [], _, i, _, hi, _, _ => False.elim (Nat.not_lt_zero i hi)
  | x :: xs, hNd, 0, 0, _, _, _ => rfl
  | x :: xs, hNd, 0, j + 1, _, hj, hEq => by
    obtain ⟨hNotMem, _⟩ := List.nodup_cons.mp hNd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
    exact False.elim (hNotMem (hEq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)))
  | x :: xs, hNd, i + 1, 0, hi, _, hEq => by
    obtain ⟨hNotMem, _⟩ := List.nodup_cons.mp hNd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
    exact False.elim (hNotMem (hEq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)))
  | x :: xs, hNd, i + 1, j + 1, hi, hj, hEq => by
    obtain ⟨_, hNdTail⟩ := List.nodup_cons.mp hNd
    simp only [List.getElem_cons_succ] at hEq
    exact congrArg Nat.succ
      (nodup_getElem_inj hNdTail (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) hEq)

section SelectorEquiv

attribute [local irreducible] allStepConstraintKinds stepOpGuardResiduals stepOpExpectedNext
  stepOpPermTrace stepOpBoundaryResiduals stepOpConstraints

private theorem oneHot_getD_eq (kind : StepConstraintKind) (hMem : kind ∈ allStepConstraintKinds)
    (k : Nat) (hk : k < allStepConstraintKinds.length) :
    (oneHotStepSelectors kind).getD k Goldilocks.zero =
      if k = stepConstraintKindIdx kind then Goldilocks.one else Goldilocks.zero := by
  unfold oneHotStepSelectors stepConstraintKindIdx
  have hkMap : k < (allStepConstraintKinds.map fun x =>
      if x == kind then Goldilocks.one else Goldilocks.zero).length := by simp [hk]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkMap, Option.getD_some, List.getElem_map]
  have hIdxLt : allStepConstraintKinds.idxOf kind < allStepConstraintKinds.length :=
    List.idxOf_lt_length_of_mem hMem
  by_cases hEqIdx : k = allStepConstraintKinds.idxOf kind
  · subst hEqIdx
    have hAt : allStepConstraintKinds[allStepConstraintKinds.idxOf kind]'hIdxLt = kind :=
      List.getElem_idxOf hIdxLt
    simp [hAt]
  · have hNeElem : allStepConstraintKinds[k]'hk ≠ kind := by
      intro hSame
      apply hEqIdx
      have hAt : allStepConstraintKinds[allStepConstraintKinds.idxOf kind]'hIdxLt = kind :=
        List.getElem_idxOf hIdxLt
      exact nodup_getElem_inj allStepConstraintKinds_nodup hk hIdxLt (hSame.trans hAt.symm)
    simp [beq_false_of_ne hNeElem, hEqIdx]

/-- **One-Hot Selector Collapse (`hemStepSelector_oneHot_collapse`)**:
    Under pairwise orthogonality `s_i * s_j = 0` and scheduled pin `1 - s_{uid} = 0`,
    `sels` is forced to equal `oneHotStepSelectors kind`. -/
theorem hemStepSelector_oneHot_collapse (kind : StepConstraintKind) (sels : List Goldilocks)
    (hMem : kind ∈ allStepConstraintKinds)
    (hLen : sels.length = allStepConstraintKinds.length)
    (hOrth : allZeroGoldilocks (hemStepSelectorOrthResiduals sels) = true)
    (hPin : Goldilocks.one -ₚ sels.getD (stepConstraintKindIdx kind) Goldilocks.zero = Goldilocks.zero) :
    sels = oneHotStepSelectors kind := by
  have hOrthFn := (allZero_orth_iff sels).mp hOrth
  have hUidOne : sels.getD (stepConstraintKindIdx kind) Goldilocks.zero = Goldilocks.one :=
    (g_sub_eq_zero_iff.mp hPin).symm
  have hUidLt : stepConstraintKindIdx kind < allStepConstraintKinds.length :=
    List.idxOf_lt_length_of_mem hMem
  apply List.ext_getElem
  · rw [hLen, oneHotStepSelectors, List.length_map]
  · intro k hk1 hk2
    have hkLt : k < allStepConstraintKinds.length := hLen ▸ hk1
    have hLhs : sels[k]'hk1 = sels.getD k Goldilocks.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1, Option.getD_some]
    have hRhs : (oneHotStepSelectors kind)[k]'hk2 =
        (oneHotStepSelectors kind).getD k Goldilocks.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some]
    rw [hLhs, hRhs, oneHot_getD_eq kind hMem k hkLt]
    by_cases hEq : k = stepConstraintKindIdx kind
    · subst hEq; simpa [List.getD_eq_getElem?_getD] using hUidOne
    · simp only [hEq, ↓reduceIte]
      by_cases hLt : k < stepConstraintKindIdx kind
      · have hProd := hOrthFn (stepConstraintKindIdx kind) k hLt hUidLt
        rw [hUidOne, g_mul_one] at hProd
        exact hProd
      · have hGt : stepConstraintKindIdx kind < k := by omega
        have hProd := hOrthFn k (stepConstraintKindIdx kind) hGt hkLt
        rw [hUidOne, g_one_mul] at hProd
        exact hProd

private theorem foldl_oneHot_sum (n uid : Nat) (hUid : uid < n) (f : Nat → Goldilocks) :
    (List.range n).foldl
      (fun acc k => acc +ₚ ((if k = uid then Goldilocks.one else Goldilocks.zero) *ₚ f k))
      Goldilocks.zero = f uid := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hEq : m = uid
    · subst hEq
      have hZeroPre : ∀ (ls : List Nat), (∀ k ∈ ls, k ≠ m) →
          ls.foldl (fun acc k => acc +ₚ ((if k = m then Goldilocks.one else Goldilocks.zero) *ₚ f k))
            Goldilocks.zero = Goldilocks.zero := by
        intro ls hNe
        induction ls with
        | nil => rfl
        | cons a as ihL =>
          have haNe : a ≠ m := hNe a (List.mem_cons_self ..)
          simp only [List.foldl_cons, haNe, ↓reduceIte, g_zero_mul, g_add_zero]
          exact ihL (fun x hx => hNe x (List.mem_cons_of_mem _ hx))
      rw [hZeroPre (List.range m) (fun k hk => Nat.ne_of_lt (List.mem_range.mp hk))]
      simp only [↓reduceIte, g_one_mul, g_zero_add]
    · have hLtM : uid < m := by omega
      rw [ih hLtM]
      simp only [hEq, ↓reduceIte, g_zero_mul, g_add_zero]

private theorem getD_rep_zero :
    ∀ (n j : Nat), (List.replicate n Goldilocks.zero).getD j Goldilocks.zero = Goldilocks.zero
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, j + 1 => getD_rep_zero n j

private theorem foldl_congr_on {A B : Type} (f g : B → A → B) :
    ∀ (xs : List A) (init : B), (∀ a ∈ xs, ∀ acc, f acc a = g acc a) →
      xs.foldl f init = xs.foldl g init
  | [], _, _ => rfl
  | a :: rest, init, h =>
    (congrArg (fun acc => rest.foldl f acc) (h a (List.mem_cons_self ..) init)).trans
      (foldl_congr_on f g rest (g init a) (fun b hb acc => h b (List.mem_cons_of_mem a hb) acc))

private theorem foldl_selector_sum (n uid : Nat) (hUid : uid < n)
    (sel f : Nat → Goldilocks)
    (hSel : ∀ k < n, sel k = if k = uid then Goldilocks.one else Goldilocks.zero) :
    (List.range n).foldl (fun acc k => acc +ₚ (sel k *ₚ f k)) Goldilocks.zero = f uid := by
  have h := foldl_congr_on
    (fun acc k => acc +ₚ (sel k *ₚ f k))
    (fun acc k => acc +ₚ ((if k = uid then Goldilocks.one else Goldilocks.zero) *ₚ f k))
    (List.range n) Goldilocks.zero
    (fun k hk acc => congrArg (fun v => acc +ₚ (v *ₚ f k)) (hSel k (List.mem_range.mp hk)))
  exact h.trans (foldl_oneHot_sum n uid hUid f)

private theorem hemStep_oneHot_fold (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (hMem : kind ∈ allStepConstraintKinds) (j : Nat) :
    (List.range allStepConstraintKinds.length).foldl
      (fun acc k => acc +ₚ ((oneHotStepSelectors kind).getD k Goldilocks.zero *ₚ
        stepOpExpectedNext (allStepConstraintKinds.getD k .idle) c0 x j))
      Goldilocks.zero = stepOpExpectedNext kind c0 x j := by
  have hUidLt : stepConstraintKindIdx kind < allStepConstraintKinds.length := by
    unfold stepConstraintKindIdx
    exact List.idxOf_lt_length_of_mem hMem
  have hKindAtUid : allStepConstraintKinds.getD (stepConstraintKindIdx kind) .idle = kind := by
    have hIdxLt : allStepConstraintKinds.idxOf kind < allStepConstraintKinds.length :=
      List.idxOf_lt_length_of_mem hMem
    unfold stepConstraintKindIdx
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hIdxLt, Option.getD_some]
    exact List.getElem_idxOf hIdxLt
  have h := foldl_selector_sum allStepConstraintKinds.length (stepConstraintKindIdx kind)
    hUidLt (fun k => (oneHotStepSelectors kind).getD k Goldilocks.zero)
    (fun k => stepOpExpectedNext (allStepConstraintKinds.getD k .idle) c0 x j)
    (oneHot_getD_eq kind hMem)
  exact h.trans (congrArg (fun k => stepOpExpectedNext k c0 x j) hKindAtUid)

private theorem hemStep_oneHot_guards (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (hMem : kind ∈ allStepConstraintKinds) :
    allZeroGoldilocks ((List.range allStepConstraintKinds.length).flatMap fun k =>
      (stepOpGuardResiduals (allStepConstraintKinds.getD k .idle) c0 x).map
        (fun g => (oneHotStepSelectors kind).getD k Goldilocks.zero *ₚ g)) = true ↔
    allZeroGoldilocks (stepOpGuardResiduals kind c0 x) = true := by
  have hUidLt : stepConstraintKindIdx kind < allStepConstraintKinds.length := by
    unfold stepConstraintKindIdx
    exact List.idxOf_lt_length_of_mem hMem
  have hKindAtUid : allStepConstraintKinds.getD (stepConstraintKindIdx kind) .idle = kind := by
    have hIdxLt : allStepConstraintKinds.idxOf kind < allStepConstraintKinds.length :=
      List.idxOf_lt_length_of_mem hMem
    unfold stepConstraintKindIdx
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hIdxLt, Option.getD_some]
    exact List.getElem_idxOf hIdxLt
  constructor
  · intro hGuards
    unfold allZeroGoldilocks at hGuards ⊢
    rw [List.all_flatMap, List.all_eq_true] at hGuards
    have hAt := hGuards (stepConstraintKindIdx kind) (List.mem_range.mpr hUidLt)
    rw [oneHot_getD_eq kind hMem _ hUidLt] at hAt
    simp only [↓reduceIte, hKindAtUid, List.all_map] at hAt
    have hComp : ((fun x => x == Goldilocks.zero) ∘ fun g => Goldilocks.one *ₚ g) =
        (fun x => x == Goldilocks.zero) := by
      funext g; simp only [Function.comp, g_one_mul]
    rwa [hComp] at hAt
  · intro hGuardOk
    unfold allZeroGoldilocks at hGuardOk ⊢
    rw [List.all_flatMap, List.all_eq_true]
    intro k hkRange
    have hk := List.mem_range.mp hkRange
    rw [oneHot_getD_eq kind hMem k hk, List.all_map]
    by_cases hEq : k = stepConstraintKindIdx kind
    · simp only [hEq, ↓reduceIte, hKindAtUid]
      have hComp : ((fun x => x == Goldilocks.zero) ∘ fun g => Goldilocks.one *ₚ g) =
          (fun x => x == Goldilocks.zero) := by
        funext g; simp only [Function.comp, g_one_mul]
      rwa [hComp]
    · simp only [hEq, ↓reduceIte]
      have hComp0 : ((fun x => x == Goldilocks.zero) ∘ fun g => Goldilocks.zero *ₚ g) =
          (fun _ => true) := by
        funext g; simp only [Function.comp, g_zero_mul, beq_self_eq_true]
      rw [hComp0]
      exact List.all_eq_true.mpr (fun _ _ => rfl)

private theorem hemStep_oneHot_mux (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (hMem : kind ∈ allStepConstraintKinds)
    (hValid : kind.validSlot = true) :
    allZeroGoldilocks (hemStepMuxedInputResiduals c0 x (oneHotStepSelectors kind)) = true ↔
    allZeroGoldilocks (stepOpConstraints kind c0 x) = true := by
  unfold hemStepMuxedInputResiduals
  rw [allZeroGoldilocks_append, Bool.and_eq_true, hemStep_oneHot_guards kind c0 x hMem,
    stepOpConstraints_iff_guard_and_next kind c0 x hValid]
  apply and_congr_right'
  rw [allZero_map_iff]
  constructor
  · intro h j hj
    exact (g_sub_eq_zero_iff.mp (h j hj)).trans (hemStep_oneHot_fold kind c0 x hMem j)
  · intro h j hj
    exact g_sub_eq_zero_iff.mpr ((h j hj).trans (hemStep_oneHot_fold kind c0 x hMem j).symm)

private theorem hemStep_oneHot_selectors (kind : StepConstraintKind)
    (hMem : kind ∈ allStepConstraintKinds) :
    allZeroGoldilocks (hemStepSelectorBoolResiduals (oneHotStepSelectors kind)) = true ∧
    allZeroGoldilocks (hemStepSelectorOrthResiduals (oneHotStepSelectors kind)) = true ∧
    Goldilocks.one -ₚ (oneHotStepSelectors kind).getD (stepConstraintKindIdx kind) Goldilocks.zero =
      Goldilocks.zero := by
  have hUidLt : stepConstraintKindIdx kind < allStepConstraintKinds.length := by
    unfold stepConstraintKindIdx
    exact List.idxOf_lt_length_of_mem hMem
  refine ⟨?_, ?_, ?_⟩
  · unfold hemStepSelectorBoolResiduals
    rw [allZero_map_iff]; intro k hk
    rw [oneHot_getD_eq kind hMem k hk]
    by_cases hEq : k = stepConstraintKindIdx kind
    · simp only [hEq, ↓reduceIte]
      exact (stepBoolCheck_eq_zero_iff _).mpr (.inr rfl)
    · simp only [hEq, ↓reduceIte]
      exact (stepBoolCheck_eq_zero_iff _).mpr (.inl rfl)
  · rw [allZero_orth_iff]; intro i j hji hi
    rw [oneHot_getD_eq kind hMem j (Nat.lt_trans hji hi), oneHot_getD_eq kind hMem i hi]
    by_cases hjU : j = stepConstraintKindIdx kind
    · have hiNe : i ≠ stepConstraintKindIdx kind := by omega
      simp only [hjU, hiNe, ↓reduceIte]
      exact g_mul_zero _
    · simp only [hjU, ↓reduceIte]
      exact g_zero_mul _
  · rw [oneHot_getD_eq kind hMem _ hUidLt]
    simp only [↓reduceIte]
    exact g_sub_self _

private theorem hemStepSelectorInputs_iff (kind : StepConstraintKind) (c0 : Goldilocks)
    (x : StepOpRowInputs) (sels : List Goldilocks) (permRes boundaryRes : List Goldilocks)
    (hMem : kind ∈ allStepConstraintKinds) (hValid : kind.validSlot = true)
    (hLen : sels.length = allStepConstraintKinds.length) :
    allZeroGoldilocks
        (permRes ++
         boundaryRes ++
         hemStepSelectorBoolResiduals sels ++
         hemStepSelectorOrthResiduals sels ++
         [Goldilocks.one -ₚ sels.getD (stepConstraintKindIdx kind) Goldilocks.zero] ++
         hemStepMuxedInputResiduals c0 x sels) = true ↔
      allZeroGoldilocks
        (permRes ++
         boundaryRes ++
         stepOpConstraints kind c0 x) = true ∧
      sels = oneHotStepSelectors kind := by
  have hSingle : ∀ r : Goldilocks, allZeroGoldilocks [r] = (r == Goldilocks.zero) := by
    intro r; simp [allZeroGoldilocks]
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, hSingle, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨hGA, hBnd⟩, _⟩, hOrth⟩, hPin⟩, hMux⟩
    have hEq := hemStepSelector_oneHot_collapse kind sels hMem hLen hOrth hPin
    rw [hEq] at hMux
    exact ⟨⟨⟨hGA, hBnd⟩, (hemStep_oneHot_mux kind c0 x hMem hValid).mp hMux⟩, hEq⟩
  · rintro ⟨⟨⟨hGA, hBnd⟩, hOp⟩, hEq⟩
    rw [hEq]
    obtain ⟨hBool, hOrth, hPin⟩ := hemStep_oneHot_selectors kind hMem
    exact ⟨⟨⟨⟨⟨hGA, hBnd⟩, hBool⟩, hOrth⟩, hPin⟩,
      (hemStep_oneHot_mux kind c0 x hMem hValid).mpr hOp⟩


private theorem hemStepSelectorRowActive_iff (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (rowsPerSigner t : Nat) (sr : HemStepOpSelectorRow)
    (hMem : kind ∈ allStepConstraintKinds) (hValid : kind.validSlot = true)
    (hLen : sr.sels.length = allStepConstraintKinds.length) :
    allZeroGoldilocks
        ((stepOpPermTrace sr.row).2 ++
         stepOpBoundaryResiduals rowsPerSigner t sr.row ++
         hemStepSelectorBoolResiduals sr.sels ++
         hemStepSelectorOrthResiduals sr.sels ++
         [Goldilocks.one -ₚ sr.sels.getD (stepConstraintKindIdx kind) Goldilocks.zero] ++
         hemStepMuxedOpResiduals (some pub) c0 sr.row sr.sels) = true ↔
      allZeroGoldilocks
        ((stepOpPermTrace sr.row).2 ++
         stepOpBoundaryResiduals rowsPerSigner t sr.row ++
         stepOpConstraints kind c0 (stepOpRowInputs pub sr.row)) = true ∧
      sr.sels = oneHotStepSelectors kind :=
  hemStepSelectorInputs_iff kind c0 (stepOpRowInputs pub sr.row) sr.sels
    (stepOpPermTrace sr.row).2 (stepOpBoundaryResiduals rowsPerSigner t sr.row)
    hMem hValid hLen

private theorem hemStepSelectorRowResiduals_iff (profile : AggSigProfile) (slot : StepOpSlot)
    (t : Nat) (sr : HemStepOpSelectorRow)
    (hLen : sr.sels.length = allStepConstraintKinds.length) :
    allZeroGoldilocks (hemStepSelectorRowResiduals profile slot t sr) = true ↔
      allZeroGoldilocks (stepOp256RowResiduals profile slot t sr.row) = true ∧
      sr.sels = (match slot with
        | none => List.replicate allStepConstraintKinds.length Goldilocks.zero
        | some _ =>
          oneHotStepSelectors (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1) := by
  unfold hemStepSelectorRowResiduals stepOp256RowResiduals
  cases slot with
  | none =>
    unfold hemStepSchedulePinResiduals hemStepMuxedOpResiduals
    simp only [List.append_nil, allZeroGoldilocks_append, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨⟨⟨hGA, hBnd⟩, _⟩, _⟩, hPin⟩
      have hZeroAll := (allZero_map_iff allStepConstraintKinds.length
        (fun k => sr.sels.getD k Goldilocks.zero)).mp hPin
      refine ⟨⟨hGA, hBnd⟩, ?_⟩
      apply List.ext_getElem
      · rw [hLen, List.length_replicate]
      · intro k hk1 _
        have hGet : sr.sels[k]'hk1 = sr.sels.getD k Goldilocks.zero := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1, Option.getD_some]
        rw [hGet, List.getElem_replicate]
        exact hZeroAll k (hLen ▸ hk1)
    · rintro ⟨⟨hGA, hBnd⟩, hSelsEq⟩
      refine ⟨⟨⟨⟨hGA, hBnd⟩, ?_⟩, ?_⟩, ?_⟩
      · rw [hSelsEq]; unfold hemStepSelectorBoolResiduals
        rw [allZero_map_iff]; intro k _
        rw [getD_rep_zero]; exact (stepBoolCheck_eq_zero_iff _).mpr (.inl rfl)
      · rw [hSelsEq, allZero_orth_iff]; intro i j _ _
        rw [getD_rep_zero, g_zero_mul]
      · rw [hSelsEq, allZero_map_iff]; intro k _; exact getD_rep_zero _ _
  | some pub =>
    obtain ⟨hMem, hValid⟩ := buildSignerProgram_kind_mem_and_valid profile t
    unfold hemStepSchedulePinResiduals
    exact hemStepSelectorRowActive_iff
      (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1
      (Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).2)
      pub (stepOpRowsPerSigner profile) t sr hMem hValid hLen

private theorem hemStepSelectorIntraFrom_iff (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (srows : List HemStepOpSelectorRow) (g : Nat),
      (∀ sr ∈ srows, sr.sels.length = allStepConstraintKinds.length) →
      (allZeroGoldilocks (hemStepSelectorIntraFrom profile slots g srows) = true ↔
        allZeroGoldilocks (stepOp256IntraResidualsFrom profile slots g (srows.map HemStepOpSelectorRow.row)) = true ∧
        srows = attachHonestStepSelectorsFrom profile slots g (srows.map HemStepOpSelectorRow.row))
  | [], _, _ => by simp [hemStepSelectorIntraFrom, stepOp256IntraResidualsFrom, attachHonestStepSelectorsFrom]
  | sr :: rest, g, hLens => by
    simp only [List.map_cons, hemStepSelectorIntraFrom, stepOp256IntraResidualsFrom,
      attachHonestStepSelectorsFrom]
    rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true,
        hemStepSelectorRowResiduals_iff profile _ _ sr (hLens sr (List.mem_cons_self ..)),
        hemStepSelectorIntraFrom_iff profile slots rest (g + 1)
          (fun x hx => hLens x (List.mem_cons_of_mem _ hx))]
    constructor
    · rintro ⟨⟨hRowOk, hSelEq⟩, hRestOk, hRestEq⟩
      refine ⟨⟨hRowOk, hRestOk⟩, ?_⟩
      rw [← hRestEq]
      cases sr; dsimp only at hSelEq ⊢; subst hSelEq; rfl
    · rintro ⟨⟨hRowOk, hRestOk⟩, hConsEq⟩
      injection hConsEq with hHeadEq hTailEq
      have hSelEq : sr.sels = _ := (congrArg HemStepOpSelectorRow.sels hHeadEq)
      exact ⟨⟨hRowOk, hSelEq⟩, hRestOk, hTailEq⟩

private theorem attachHonestStepSelectorsFrom_map_row (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (rows : List StepOpRow) (g : Nat),
      (attachHonestStepSelectorsFrom profile slots g rows).map HemStepOpSelectorRow.row = rows
  | [], _ => rfl
  | r :: rs, g => congrArg (r :: ·) (attachHonestStepSelectorsFrom_map_row profile slots rs (g + 1))

private theorem attachHonestStepSelectorsFrom_sels_len (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (rows : List StepOpRow) (g : Nat) (sr : HemStepOpSelectorRow),
      sr ∈ attachHonestStepSelectorsFrom profile slots g rows →
      sr.sels.length = allStepConstraintKinds.length
  | [], _, _, h => False.elim (List.not_mem_nil h)
  | r :: rs, g, sr, h => by
    rcases List.mem_cons.mp h with rfl | hTail
    · dsimp only
      cases slots.getD (g / stepOpRowsPerSigner profile) none with
      | none => exact List.length_replicate
      | some _ => unfold oneHotStepSelectors; exact List.length_map ..
    · exact attachHonestStepSelectorsFrom_sels_len profile slots rs (g + 1) sr hTail

/-- **Selector-Muxed 256-Column Equivalence (`hemStepTraceValid_iff_stepOp256TableOk`)**:
    1. Attaching canonical scheduled selectors to any `rows` satisfies `hemStepTraceValid` iff
       `stepOp256TableOk profile slots rows = true`.
    2. Conversely, ANY selector-explicit trace `srows` satisfying `hemStepTraceValid` has
       `srows = attachHonestStepSelectors profile slots (srows.map (·.row))` and
       `stepOp256TableOk profile slots (srows.map (·.row)) = true`. -/
theorem hemStepTraceValid_iff_stepOp256TableOk (profile : AggSigProfile) (slots : List StepOpSlot)
    (srows : List HemStepOpSelectorRow) :
    hemStepTraceValid profile slots srows = true ↔
      stepOp256TableOk profile slots (srows.map HemStepOpSelectorRow.row) = true ∧
      srows = attachHonestStepSelectors profile slots (srows.map HemStepOpSelectorRow.row) := by
  unfold hemStepTraceValid stepOp256TableOk attachHonestStepSelectors
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_map, List.all_map, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨hPos, hLen⟩, hShapedAndSels⟩, hIntra⟩, hShift⟩
    have hShaped : ∀ x ∈ srows, x.row.wellShaped = true := fun x hx => (hShapedAndSels x hx).1
    have hSelsLen : ∀ x ∈ srows, x.sels.length = allStepConstraintKinds.length :=
      fun x hx => (hShapedAndSels x hx).2
    obtain ⟨hIntraRow, hSrowsEq⟩ := (hemStepSelectorIntraFrom_iff profile slots srows 0 hSelsLen).mp hIntra
    exact ⟨⟨⟨⟨⟨hPos, hLen⟩, hShaped⟩, hIntraRow⟩, hShift⟩, hSrowsEq⟩
  · rintro ⟨⟨⟨⟨⟨hPos, hLen⟩, hShaped⟩, hIntraRow⟩, hShift⟩, hSrowsEq⟩
    have hSelsLen : ∀ x ∈ srows, x.sels.length = allStepConstraintKinds.length := by
      intro x hx
      rw [hSrowsEq] at hx
      exact attachHonestStepSelectorsFrom_sels_len profile slots _ 0 x hx
    have hIntra := (hemStepSelectorIntraFrom_iff profile slots srows 0 hSelsLen).mpr ⟨hIntraRow, hSrowsEq⟩
    exact ⟨⟨⟨⟨hPos, hLen⟩, fun x hx => ⟨hShaped x hx, hSelsLen x hx⟩⟩, hIntra⟩, hShift⟩

theorem hemStepTraceValid_attachHonest_iff (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) :
    hemStepTraceValid profile slots (attachHonestStepSelectors profile slots rows) = true ↔
      stepOp256TableOk profile slots rows = true := by
  rw [hemStepTraceValid_iff_stepOp256TableOk]
  unfold attachHonestStepSelectors
  rw [attachHonestStepSelectorsFrom_map_row]
  simp

end SelectorEquiv

/-- A valid active table row executes the scheduled functional transition and satisfies
    its guards; its permutation output is the actual Poseidon2 permutation. This theorem
    projects facts from the original table, without adding a verifier-validity premise. -/
theorem stepOp256TableOk_active_execution (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (i : Nat) (row : StepOpRow) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hRow : rows[i]? = some row)
    (hSlot : slots.getD (i / stepOpRowsPerSigner profile) none = some pub) :
    let op := (buildSignerProgram profile).getD (i % stepOpRowsPerSigner profile) StepOp.idle
    let kind := (stepOpKindAndC0 op).1
    let c0 := Goldilocks.ofNat (stepOpKindAndC0 op).2
    (stepOpPermTrace row).1 = poseidon2Perm12 row.stIn ∧
    allZeroGoldilocks (stepOpGuardResiduals kind c0 (stepOpRowInputs pub row)) = true ∧
    ∀ j < 44, row.nextState.getD j Goldilocks.zero =
      stepOpExpectedNext kind c0 (stepOpRowInputs pub row) j := by
  have hr := stepOp256TableOk_row_at profile slots rows i row hTable hRow
  unfold stepOp256RowResiduals at hr
  rw [hSlot] at hr
  simp only [allZeroGoldilocks_append, Bool.and_eq_true] at hr
  obtain ⟨_, hValid⟩ := buildSignerProgram_kind_mem_and_valid profile
    (i % stepOpRowsPerSigner profile)
  exact ⟨stepOp256_groupA_exact row hr.1.1,
    (stepOpConstraints_iff_guard_and_next _ _ _ hValid).mp hr.2⟩

/-- Populate the 44 next-state cells by executing an opcode. The remaining 212 cells
    are retained. This is an execution constructor, not a native-signature trace builder. -/
def populateStepOpNext (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow) : StepOpRow :=
  { row with nextState := (List.range 44).map (stepOpExpectedNext kind c0 (stepOpRowInputs pub row)) }

private theorem populateStepOpNext_inputs (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow) :
    stepOpRowInputs pub (populateStepOpNext kind c0 pub row) =
      { stepOpRowInputs pub row with next := fun j =>
          ((List.range 44).map (stepOpExpectedNext kind c0 (stepOpRowInputs pub row))).getD j Goldilocks.zero } := rfl

/-- Every scheduled opcode admits exactly its functional next state once its guards
    hold. This covers all active opcode classes, rather than just padding `Idle`. -/
theorem populateStepOpNext_constraints_iff (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow)
    (hValid : kind.validSlot = true) :
    allZeroGoldilocks (stepOpConstraints kind c0
      (stepOpRowInputs pub (populateStepOpNext kind c0 pub row))) = true ↔
    allZeroGoldilocks (stepOpGuardResiduals kind c0 (stepOpRowInputs pub row)) = true := by
  rw [stepOpConstraints_iff_guard_and_next kind c0 _ hValid,
    populateStepOpNext_inputs, stepOpGuardResiduals_congr_next]
  have hNext : ∀ j < 44,
      (stepOpRowInputs pub (populateStepOpNext kind c0 pub row)).next j =
        stepOpExpectedNext kind c0 (stepOpRowInputs pub row) j := by
    intro j hj
    simp [stepOpRowInputs, populateStepOpNext, List.getD_eq_getElem?_getD, hj]
  constructor
  · exact And.left
  · intro hGuard
    refine ⟨hGuard, ?_⟩
    intro j hj
    rw [stepOpExpectedNext_congr_next]
    exact hNext j hj

/-- An accepted row is unchanged by recomputing its next-state block. In particular,
    the AIR cannot accept two different 44-cell next states for the same guarded inputs. -/
theorem populateStepOpNext_eq_of_constraints (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow)
    (hValid : kind.validSlot = true) (hLen : row.nextState.length = 44)
    (hOk : allZeroGoldilocks (stepOpConstraints kind c0 (stepOpRowInputs pub row)) = true) :
    populateStepOpNext kind c0 pub row = row := by
  have hNext := ((stepOpConstraints_iff_guard_and_next kind c0 _ hValid).mp hOk).2
  have hEq : (List.range 44).map (stepOpExpectedNext kind c0 (stepOpRowInputs pub row)) =
      row.nextState := by
    apply List.ext_getElem
    · simp [hLen]
    · intro i hi hi'
      have hi44 : i < 44 := by simpa using hi
      have he := hNext i hi44
      simpa [stepOpRowInputs, List.getD_eq_getElem?_getD, hi'] using he.symm
  simp [populateStepOpNext, hEq]

/-- Guard/transition completeness for a scheduled active row, with both boundary gates
    retained. Native-verifier completeness still requires constructing inputs satisfying
    these guards along the complete signer program. -/
theorem stepOp256RowResiduals_active_iff (profile : AggSigProfile)
    (pub : AggValidatorPk × Digest5) (t : Nat) (row : StepOpRow) :
    let op := (buildSignerProgram profile).getD t StepOp.idle
    let kind := (stepOpKindAndC0 op).1
    let c0 := Goldilocks.ofNat (stepOpKindAndC0 op).2
    allZeroGoldilocks (stepOp256RowResiduals profile (some pub) t row) = true ↔
      allZeroGoldilocks (stepOpPermTrace row).2 = true ∧
      (∀ j < 44, t = 0 → row.prevState.getD j Goldilocks.zero = Goldilocks.zero) ∧
      (∀ j < 44, t + 1 = stepOpRowsPerSigner profile →
        row.nextState.getD j Goldilocks.zero = Goldilocks.zero) ∧
      allZeroGoldilocks (stepOpGuardResiduals kind c0 (stepOpRowInputs pub row)) = true ∧
      (∀ j < 44, row.nextState.getD j Goldilocks.zero =
        stepOpExpectedNext kind c0 (stepOpRowInputs pub row) j) := by
  dsimp only
  unfold stepOp256RowResiduals
  rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true,
    stepOpBoundaryResiduals_iff, stepOpConstraints_iff_guard_and_next _ _ _
      (buildSignerProgram_kind_mem_and_valid profile t).2]
  simp only [and_assoc, stepOpRowInputs]

/-- A corrupted next-state limb is rejected even when the other row cells are arbitrary.
    This pairs with the constructor above: the transition gate enforces its computed output. -/
theorem tooth_stepOp_wrong_next_rejected (kind : StepConstraintKind) (c0 : Goldilocks)
    (pub : AggValidatorPk × Digest5) (row : StepOpRow) (j : Nat)
    (hValid : kind.validSlot = true) (hj : j < 44)
    (hWrong : row.nextState.getD j Goldilocks.zero ≠
      stepOpExpectedNext kind c0 (stepOpRowInputs pub row) j) :
    allZeroGoldilocks (stepOpConstraints kind c0 (stepOpRowInputs pub row)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact hWrong (((stepOpConstraints_iff_guard_and_next kind c0 _ hValid).mp h).2 j hj)

/-- Populate all permutation columns without assuming any opcode guards. -/
def stepOpHonestPermutationRow (input : Poseidon2State12)
    (prev next aux : List Goldilocks) : StepOpRow :=
  let w := honestPoseidon2PermWitness input
  ⟨input, w.initExtSbox, w.intSbox, w.termExtSbox, prev, next, aux⟩

theorem stepOpHonestPermutationRow_groupA (input : Poseidon2State12)
    (prev next aux : List Goldilocks) :
    allZeroGoldilocks (stepOpPermTrace (stepOpHonestPermutationRow input prev next aux)).2 = true := by
  let w := honestPoseidon2PermWitness input
  have h := (poseidon2PermResiduals_allZero_iff w).mpr rfl
  have he : poseidon2PermResiduals w =
      (stepOpPermTrace (stepOpHonestPermutationRow input prev next aux)).2 ++
      (state12Sub (stepOpPermTrace (stepOpHonestPermutationRow input prev next aux)).1
        w.output).toList := rfl
  rw [he, allZeroGoldilocks_append, Bool.and_eq_true] at h
  exact h.1

theorem stepOpHonestPermutationRow_wellShaped (input : Poseidon2State12)
    (prev next aux : List Goldilocks)
    (hp : prev.length = 44) (hn : next.length = 44) (ha : aux.length = 38) :
    (stepOpHonestPermutationRow input prev next aux).wellShaped = true := by
  have h1 : (honestPoseidon2PermWitness input).initExtSbox.length = 4 := rfl
  have h2 : (honestPoseidon2PermWitness input).intSbox.length = 22 := rfl
  have h3 : (honestPoseidon2PermWitness input).termExtSbox.length = 4 := rfl
  simp only [stepOpHonestPermutationRow, StepOpRow.wellShaped, h1, h2, h3, hp, hn, ha,
    beq_self_eq_true, Bool.and_self]

/-- A non-padding active opcode has satisfiable guards and a full honest permutation
    witness. This certificate concerns one row; it does not assert a valid whole signer slot. -/
theorem inhabited_populateStepOpNext :
    ∃ (kind : StepConstraintKind) (c0 : Goldilocks)
      (pub : AggValidatorPk × Digest5) (row : StepOpRow),
      kind.validSlot = true ∧ kind ≠ .idle ∧
      allZeroGoldilocks (stepOpGuardResiduals kind c0 (stepOpRowInputs pub row)) = true ∧
      row.wellShaped = true ∧
      allZeroGoldilocks (stepOpPermTrace row).2 = true := by
  let pub : AggValidatorPk × Digest5 :=
    (⟨.corduroyPoseidon2, ⟨‹1›, ‹2›, ‹3›, ‹4›⟩, ⟨‹5›, ‹6›, ‹7›, ‹8›⟩⟩,
      ⟨‹9›, ‹10›, ‹11›, ‹12›, ‹13›⟩)
  let input : Poseidon2State12 :=
    ⟨pub.1.pkSeed, pub.1.pkRoot, ⟨domainHMsgStateless, pub.2.limb4, Goldilocks.zero, poseidon2IvTag⟩⟩
  let row := stepOpHonestPermutationRow input (List.replicate 44 Goldilocks.zero)
    (List.replicate 44 Goldilocks.zero) (List.replicate 38 Goldilocks.zero)
  refine ⟨.statelessDeriveBlock0, Goldilocks.zero, pub, row, rfl, by decide, ?_, ?_, ?_⟩
  · change allZeroGoldilocks (stepOpGuardResiduals .statelessDeriveBlock0 Goldilocks.zero
      (stepOpRowInputs pub row)) = true
    decide +kernel
  · exact stepOpHonestPermutationRow_wellShaped input _ _ _
      (List.length_replicate ..) (List.length_replicate ..) (List.length_replicate ..)
  · exact stepOpHonestPermutationRow_groupA input _ _ _

#tooth_pair populateStepOpNext_constraints_iff vs tooth_stepOp_wrong_next_rejected
#verify_inhabited populateStepOpNext_constraints_iff inhabited_populateStepOpNext

/-! ### §3.4. Active-slot execution: per-signer row semantics

`stepOp256TableOk` speaks about one flat list of rows. The lemmas below restrict it to one
active signer slot, re-index its rows by the step `t` of `buildSignerProgram`, and expose every
scheduled row as a guarded functional transition of the 44 carried limbs. -/

/-- Row `t` of signer slot `k` of a table (`stepOpZeroRow` outside the table). -/
def stepOpSlotRow (profile : AggSigProfile) (rows : List StepOpRow) (k t : Nat) : StepOpRow :=
  rows.getD (k * stepOpRowsPerSigner profile + t) stepOpZeroRow

/-- State limb `j` entering row `t`. -/
def stepPrev (R : Nat → StepOpRow) (t j : Nat) : Goldilocks :=
  (R t).prevState.getD j Goldilocks.zero

/-- Auxiliary cell `i` of row `t`. -/
def stepAux (R : Nat → StepOpRow) (t i : Nat) : Goldilocks :=
  (R t).aux.getD i Goldilocks.zero

/-- Row `t` executes `op`: its permutation columns hold `poseidon2Perm12` of its `COL_ST_IN`
    block, the guards of `op` vanish, and the state entering row `t + 1` is the functional
    next state of `op`. -/
def StepRowSem (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow) (op : StepOp)
    (t : Nat) : Prop :=
  (stepOpPermTrace (R t)).1 = poseidon2Perm12 (R t).stIn ∧
  allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
    (Goldilocks.ofNat (stepOpKindAndC0 op).2) (stepOpRowInputs pub (R t))) = true ∧
  ∀ j < 44, stepPrev R (t + 1) j =
    stepOpExpectedNext (stepOpKindAndC0 op).1 (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs pub (R t)) j

private theorem stepOpRowsPerSigner_pos (profile : AggSigProfile) :
    0 < stepOpRowsPerSigner profile := by
  cases profile <;> decide

private theorem stepOp256TableOk_slot_row_core (profile : AggSigProfile)
    (slots : List StepOpSlot) (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hSlot : slots[k]? = some (some pub)) (t : Nat)
    (ht : t < stepOpRowsPerSigner profile) :
    rows[k * stepOpRowsPerSigner profile + t]? = some (stepOpSlotRow profile rows k t) ∧
    allZeroGoldilocks (stepOp256RowResiduals profile (some pub) t
      (stepOpSlotRow profile rows k t)) = true := by
  obtain ⟨_, hLen, _, hIntra, _⟩ := (stepOp256TableOk_iff_rows profile slots rows).mp hTable
  have hRpos := stepOpRowsPerSigner_pos profile
  have hk : k < slots.length := (List.getElem?_eq_some_iff.mp hSlot).1
  have h1 : (k + 1) * stepOpRowsPerSigner profile ≤ slots.length * stepOpRowsPerSigner profile :=
    Nat.mul_le_mul_right _ hk
  rw [Nat.succ_mul] at h1
  have hi0 : k * stepOpRowsPerSigner profile + t < rows.length := by omega
  have hRow0 : rows[k * stepOpRowsPerSigner profile + t]? =
      some (stepOpSlotRow profile rows k t) := by
    unfold stepOpSlotRow
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi0]
    rfl
  have hDiv : (k * stepOpRowsPerSigner profile + t) / stepOpRowsPerSigner profile = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hRpos, Nat.div_eq_of_lt ht, Nat.zero_add]
  have hMod : (k * stepOpRowsPerSigner profile + t) % stepOpRowsPerSigner profile = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  have hSlotD : slots.getD k none = some pub := by
    rw [List.getD_eq_getElem?_getD, hSlot]
    rfl
  have hRes := hIntra _ _ hRow0
  rw [hDiv, hMod, hSlotD] at hRes
  exact ⟨hRow0, hRes⟩

/-- Every non-final row of an active slot of a valid table executes its scheduled opcode. -/
theorem stepOp256TableOk_slot_rowSem (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hSlot : slots[k]? = some (some pub)) (t : Nat)
    (ht : t + 1 < stepOpRowsPerSigner profile) :
    StepRowSem pub (stepOpSlotRow profile rows k)
      ((buildSignerProgram profile).getD t StepOp.idle) t := by
  obtain ⟨hRow0, hRes⟩ := stepOp256TableOk_slot_row_core profile slots rows k pub hTable hSlot t
    (by omega)
  obtain ⟨hRow1, _⟩ := stepOp256TableOk_slot_row_core profile slots rows k pub hTable hSlot
    (t + 1) ht
  obtain ⟨_, _, _, _, hShift⟩ := (stepOp256TableOk_iff_rows profile slots rows).mp hTable
  have hA := stepOp256RowResiduals_active_iff profile pub t (stepOpSlotRow profile rows k t)
  dsimp only at hA
  obtain ⟨hGA, _, _, hGuard, hNext⟩ := hA.mp hRes
  refine ⟨stepOp256_groupA_exact _ hGA, hGuard, fun j hj => ?_⟩
  unfold stepPrev
  rw [← hShift _ _ _ hRow0 hRow1 j hj]
  exact hNext j hj

/-- The first row of an active slot of a valid table starts from the zero state. -/
theorem stepOp256TableOk_slot_init (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hSlot : slots[k]? = some (some pub)) :
    ∀ j < 44, stepPrev (stepOpSlotRow profile rows k) 0 j = Goldilocks.zero := by
  obtain ⟨_, hRes⟩ := stepOp256TableOk_slot_row_core profile slots rows k pub hTable hSlot 0
    (stepOpRowsPerSigner_pos profile)
  have hA := stepOp256RowResiduals_active_iff profile pub 0 (stepOpSlotRow profile rows k 0)
  dsimp only at hA
  obtain ⟨_, hInit, _⟩ := hA.mp hRes
  exact fun j hj => hInit j hj rfl

/-- The rows from `t0` on execute the opcodes `ops` in order. -/
def StepRunAt (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow) (ops : List StepOp)
    (t0 : Nat) : Prop :=
  ∀ (i : Nat) (hi : i < ops.length), StepRowSem pub R ops[i] (t0 + i)

private theorem StepRunAt.head {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {ops : List StepOp} {t0 : Nat} (h : StepRunAt pub R (op :: ops) t0) :
    StepRowSem pub R op t0 :=
  h 0 (Nat.zero_lt_succ _)

private theorem StepRunAt.tail {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {ops : List StepOp} {t0 : Nat} (h : StepRunAt pub R (op :: ops) t0) :
    StepRunAt pub R ops (t0 + 1) := by
  intro i hi
  have h' := h (i + 1) (Nat.succ_lt_succ hi)
  simp only [List.getElem_cons_succ] at h'
  have e : t0 + (i + 1) = t0 + 1 + i := by omega
  rw [e] at h'
  exact h'

private theorem StepRunAt.append_left {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {a b : List StepOp} {t0 : Nat} (h : StepRunAt pub R (a ++ b) t0) :
    StepRunAt pub R a t0 := by
  intro i hi
  have h' := h i (by rw [List.length_append]; omega)
  rw [List.getElem_append_left hi] at h'
  exact h'

private theorem StepRunAt.append_right {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {a b : List StepOp} {t0 : Nat} (h : StepRunAt pub R (a ++ b) t0) :
    StepRunAt pub R b (t0 + a.length) := by
  intro i hi
  have h' := h (a.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (by omega)] at h'
  simp only [Nat.add_sub_cancel_left] at h'
  rw [← Nat.add_assoc] at h'
  exact h'

private theorem flatMap_range_uniform_length (f : Nat → List StepOp) (L : Nat)
    (hL : ∀ i, (f i).length = L) :
    ∀ n : Nat, ((List.range n).flatMap f).length = n * L
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      flatMap_range_uniform_length f L hL n, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, hL n, Nat.succ_mul]

private theorem StepRunAt.flatMap_range {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {f : Nat → List StepOp} {L : Nat} (hL : ∀ i, (f i).length = L) :
    ∀ (n : Nat) {t0 : Nat}, StepRunAt pub R ((List.range n).flatMap f) t0 →
      ∀ i < n, StepRunAt pub R (f i) (t0 + i * L)
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, t0, h, i, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at h
    by_cases hin : i < n
    · exact StepRunAt.flatMap_range hL n h.append_left i hin
    · have hEq : i = n := by omega
      subst hEq
      have h' := h.append_right
      rw [flatMap_range_uniform_length f L hL i] at h'
      exact h'

private theorem StepRunAt.map_range {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {g : Nat → StepOp} {n t0 : Nat} (h : StepRunAt pub R ((List.range n).map g) t0) :
    ∀ i < n, StepRowSem pub R (g i) (t0 + i) := by
  intro i hi
  have h' := h i (by rw [List.length_map, List.length_range]; exact hi)
  rw [List.getElem_map, List.getElem_range] at h'
  exact h'

/-- The rows of an active slot of a valid table execute the signer program body. -/
theorem stepOp256TableOk_slot_run (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hTable : stepOp256TableOk profile slots rows = true)
    (hSlot : slots[k]? = some (some pub)) :
    StepRunAt pub (stepOpSlotRow profile rows k) (signerProgramBody profile) 0 := by
  intro i hi
  have hLt : (signerProgramBody profile).length + 1 < stepOpRowsPerSigner profile := by
    cases profile with
    | xmssPoseidon2 => rw [buildSignerProgram_length.1]; decide
    | corduroyPoseidon2 => rw [buildSignerProgram_length.2.1]; decide
  have h := stepOp256TableOk_slot_rowSem profile slots rows k pub hTable hSlot i (by omega)
  have hGet : (buildSignerProgram profile).getD i StepOp.idle = (signerProgramBody profile)[i] := by
    unfold buildSignerProgram
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
    rfl
  rw [hGet] at h
  rw [Nat.zero_add]
  exact h


/-! ### §3.5. Register view of the 44 carried limbs and per-opcode row semantics -/

private theorem allZero_nil : allZeroGoldilocks [] = true := rfl

private theorem allZero_cons (r : Goldilocks) (rs : List Goldilocks) :
    allZeroGoldilocks (r :: rs) = ((r == Goldilocks.zero) && allZeroGoldilocks rs) := rfl

private theorem allZero_getElem {l : List Goldilocks} (h : allZeroGoldilocks l = true)
    (k : Nat) (hk : k < l.length) : l[k] = Goldilocks.zero := by
  unfold allZeroGoldilocks at h
  exact beq_iff_eq.mp (List.all_eq_true.mp h _ (List.getElem_mem hk))

private theorem g_ofNat_self (a : Goldilocks) : Goldilocks.ofNat a.val = a :=
  Goldilocks.ext (Nat.mod_eq_of_lt a.isLt)

private theorem g_sub_zero (a : Goldilocks) : a -ₚ Goldilocks.zero = a :=
  LawfulCommRing.sub_zero a

/-- The six `ST_REM_PACK` limbs. -/
structure StepRem where
  r0 : Goldilocks
  r1 : Goldilocks
  r2 : Goldilocks
  r3 : Goldilocks
  r4 : Goldilocks
  r5 : Goldilocks

/-- Limb `i` of `ST_REM_PACK` (zero outside the block). -/
def StepRem.get (m : StepRem) : Nat → Goldilocks
  | 0 => m.r0
  | 1 => m.r1
  | 2 => m.r2
  | 3 => m.r3
  | 4 => m.r4
  | 5 => m.r5
  | _ => Goldilocks.zero

/-- Overwrite limb `i` of `ST_REM_PACK`. -/
def StepRem.set (m : StepRem) (i : Nat) (v : Goldilocks) : StepRem :=
  match i with
  | 0 => { m with r0 := v }
  | 1 => { m with r1 := v }
  | 2 => { m with r2 := v }
  | 3 => { m with r3 := v }
  | 4 => { m with r4 := v }
  | 5 => { m with r5 := v }
  | _ => m

theorem StepRem.get_set (m : StepRem) (i j : Nat) (v : Goldilocks) (hi : i < 6) :
    (m.set i v).get j = if j = i then v else m.get j := by
  rcases i with _ | _ | _ | _ | _ | _ | i
  all_goals first
    | omega
    | (rcases j with _ | _ | _ | _ | _ | _ | j <;> first | rfl | (simp [StepRem.get, StepRem.set]))

/-- The carried state `st[0..44]` grouped by the register blocks of `trace.rs`. -/
structure StepRegs where
  curRoot : Lane4
  kp      : Goldilocks
  treeLo  : Goldilocks
  treeHi  : Goldilocks
  rem     : StepRem
  main    : Poseidon2State12
  sub     : Poseidon2State12
  work    : Lane4
  cursor  : Goldilocks
  acc     : Goldilocks
  u2      : Goldilocks

/-- Register view of a limb assignment. -/
def stepRegs (s : Nat → Goldilocks) : StepRegs :=
  { curRoot := ⟨s 0, s 1, s 2, s 3⟩
    kp := s 4
    treeLo := s 5
    treeHi := s 6
    rem := ⟨s 7, s 8, s 9, s 10, s 11, s 12⟩
    main := ⟨⟨s 13, s 14, s 15, s 16⟩, ⟨s 17, s 18, s 19, s 20⟩, ⟨s 21, s 22, s 23, s 24⟩⟩
    sub := ⟨⟨s 25, s 26, s 27, s 28⟩, ⟨s 29, s 30, s 31, s 32⟩, ⟨s 33, s 34, s 35, s 36⟩⟩
    work := ⟨s 37, s 38, s 39, s 40⟩
    cursor := s 41
    acc := s 42
    u2 := s 43 }

private theorem stepRegs_congr {s s' : Nat → Goldilocks} (h : ∀ j < 44, s j = s' j) :
    stepRegs s = stepRegs s' := by
  unfold stepRegs
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide), h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide), h 28 (by decide), h 29 (by decide), h 30 (by decide), h 31 (by decide), h 32 (by decide), h 33 (by decide), h 34 (by decide), h 35 (by decide), h 36 (by decide), h 37 (by decide), h 38 (by decide), h 39 (by decide), h 40 (by decide), h 41 (by decide), h 42 (by decide), h 43 (by decide)]

/-- Registers entering row `t`. -/
def stepRegsAt (R : Nat → StepOpRow) (t : Nat) : StepRegs := stepRegs (stepPrev R t)

/-- `poseidon2Perm12` of the `COL_ST_IN` block of row `t`. -/
def stepPermAt (R : Nat → StepOpRow) (t : Nat) : Poseidon2State12 := poseidon2Perm12 (R t).stIn

/-- Four consecutive auxiliary cells of row `t`. -/
def stepAuxLane (R : Nat → StepOpRow) (t base : Nat) : Lane4 :=
  ⟨stepAux R t base, stepAux R t (base + 1), stepAux R t (base + 2), stepAux R t (base + 3)⟩

/-- Limbwise selection `u * a + (1 - u) * c`. -/
def lane4Mux (u : Goldilocks) (a c : Lane4) : Lane4 :=
  ⟨(u *ₚ a.x0) +ₚ ((Goldilocks.one -ₚ u) *ₚ c.x0),
   (u *ₚ a.x1) +ₚ ((Goldilocks.one -ₚ u) *ₚ c.x1),
   (u *ₚ a.x2) +ₚ ((Goldilocks.one -ₚ u) *ₚ c.x2),
   (u *ₚ a.x3) +ₚ ((Goldilocks.one -ₚ u) *ₚ c.x3)⟩

theorem lane4Mux_one (a c : Lane4) : lane4Mux Goldilocks.one a c = a := by
  unfold lane4Mux
  simp only [g_sub_self, g_zero_mul, g_add_zero, g_one_mul]

theorem lane4Mux_zero (a c : Lane4) : lane4Mux Goldilocks.zero a c = c := by
  unfold lane4Mux
  simp only [g_sub_zero, g_zero_mul, g_zero_add, g_one_mul]

/-- Row inputs with the permutation output replaced by `poseidon2Perm12` of `COL_ST_IN`. -/
def stepOpRowInputsPerm (pub : AggValidatorPk × Digest5) (row : StepOpRow) : StepOpRowInputs :=
  { stepOpRowInputs pub row with
    permOut := fun i => (poseidon2Perm12 row.stIn).toList.getD i Goldilocks.zero }

private theorem StepRowSem.inputs {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {t : Nat} (h : StepRowSem pub R op t) :
    stepOpRowInputs pub (R t) = stepOpRowInputsPerm pub (R t) := by
  unfold stepOpRowInputsPerm stepOpRowInputs
  rw [h.1]

private theorem StepRowSem.guard {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {t : Nat} (h : StepRowSem pub R op t) :
    allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2) (stepOpRowInputsPerm pub (R t))) = true := by
  rw [← h.inputs]
  exact h.2.1

private theorem StepRowSem.regs {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {op : StepOp} {t : Nat} (h : StepRowSem pub R op t) :
    stepRegsAt R (t + 1) =
      stepRegs (stepOpExpectedNext (stepOpKindAndC0 op).1
        (Goldilocks.ofNat (stepOpKindAndC0 op).2) (stepOpRowInputsPerm pub (R t))) := by
  rw [← h.inputs]
  exact stepRegs_congr h.2.2

private theorem state12_ext12 {s : Poseidon2State12}
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Goldilocks}
    (h0 : s.b0.x0 = a0) (h1 : s.b0.x1 = a1) (h2 : s.b0.x2 = a2) (h3 : s.b0.x3 = a3)
    (h4 : s.b1.x0 = a4) (h5 : s.b1.x1 = a5) (h6 : s.b1.x2 = a6) (h7 : s.b1.x3 = a7)
    (h8 : s.b2.x0 = a8) (h9 : s.b2.x1 = a9) (h10 : s.b2.x2 = a10) (h11 : s.b2.x3 = a11) :
    s = ⟨⟨a0, a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩, ⟨a8, a9, a10, a11⟩⟩ :=
  Poseidon2State12.ext (Lane4.ext h0 h1 h2 h3) (Lane4.ext h4 h5 h6 h7) (Lane4.ext h8 h9 h10 h11)

local macro "gz% " h:ident k:num : term =>
  `(g_sub_eq_zero_iff.mp (allZero_getElem $h $k (Nat.le_of_ble_eq_true rfl)))

local macro "gzz% " h:ident k:num : term =>
  `(allZero_getElem $h $k (Nat.le_of_ble_eq_true rfl))

/-- The tweak block `[domain, addr, tree_lo, tree_hi]` of a WOTS+C chain step. -/
def stepWotsTweak (r : StepRegs) (c0 : Nat) : Lane4 :=
  ⟨domainWotsStep, ‹c0› +ₚ (r.kp *ₚ ‹2 ^ 16›), r.treeLo, r.treeHi⟩

theorem stepSem_wotsTellInit {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer t : Nat} (h : StepRowSem pub R (.wotsTellInit layer) t) :
    (R t).stIn =
      ⟨pub.1.pkSeed,
       ⟨‹layer * 2 ^ 32› +ₚ (stepRegsAt R t).kp, (stepRegsAt R t).treeLo,
        (stepRegsAt R t).treeHi, ‹128›⟩,
       ⟨domainWotsPk, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gzz% hG 9)
    (gzz% hG 10) (gz% hG 11), h.regs⟩

theorem stepSem_wotsChainStep1 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain t : Nat} (h : StepRowSem pub R (.wotsChainStep1 layer chain) t) :
    (R t).stIn =
      ⟨(stepRegsAt R t).work, pub.1.pkSeed,
       stepWotsTweak (stepRegsAt R t) (layer * 2 ^ 44 + chain * 2 ^ 4 + 1)⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        work := lane4Mux (stepRegsAt R t).acc (stepRegsAt R t).work
          (lane4Add (stepPermAt R t).b0 (stepRegsAt R t).work) } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), h.regs⟩


private theorem allZero_take {l : List Goldilocks} (h : allZeroGoldilocks l = true) (n : Nat) :
    allZeroGoldilocks (l.take n) = true := by
  unfold allZeroGoldilocks at h ⊢
  exact List.all_eq_true.mpr fun x hx => List.all_eq_true.mp h x (List.mem_of_mem_take hx)

private theorem allZero_drop {l : List Goldilocks} (h : allZeroGoldilocks l = true) (n : Nat) :
    allZeroGoldilocks (l.drop n) = true := by
  unfold allZeroGoldilocks at h ⊢
  exact List.all_eq_true.mpr fun x hx => List.all_eq_true.mp h x (List.mem_of_mem_drop hx)

/-- Limbwise selection `(1 - u) * a + u * c` (the left child of a Merkle node). -/
def lane4MuxL (u : Goldilocks) (a c : Lane4) : Lane4 :=
  ⟨((Goldilocks.one -ₚ u) *ₚ a.x0) +ₚ (u *ₚ c.x0),
   ((Goldilocks.one -ₚ u) *ₚ a.x1) +ₚ (u *ₚ c.x1),
   ((Goldilocks.one -ₚ u) *ₚ a.x2) +ₚ (u *ₚ c.x2),
   ((Goldilocks.one -ₚ u) *ₚ a.x3) +ₚ (u *ₚ c.x3)⟩

theorem lane4MuxL_zero (a c : Lane4) : lane4MuxL Goldilocks.zero a c = a := by
  unfold lane4MuxL
  simp only [g_sub_zero, g_zero_mul, g_add_zero, g_one_mul]

theorem lane4MuxL_one (a c : Lane4) : lane4MuxL Goldilocks.one a c = c := by
  unfold lane4MuxL
  simp only [g_sub_self, g_zero_mul, g_zero_add, g_one_mul]

/-- `st_in` of a final sponge squeeze: `main_sponge + [1, 0, ..]`. -/
def stepSqueezeIn (r : StepRegs) : Poseidon2State12 :=
  ⟨⟨r.main.b0.x0 +ₚ Goldilocks.one, r.main.b0.x1, r.main.b0.x2, r.main.b0.x3⟩,
   r.main.b1, r.main.b2⟩

/-- `st_in` of the second block of a 2-block Merkle node. -/
def stepMerkleBIn (r : StepRegs) : Poseidon2State12 :=
  ⟨lane4Add r.sub.b0 r.work,
   ⟨r.sub.b1.x0 +ₚ Goldilocks.one, r.sub.b1.x1 +ₚ poseidon2IvTag, r.sub.b1.x2, r.sub.b1.x3⟩,
   r.sub.b2⟩

theorem stepSem_wotsChainStep0 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain slot t : Nat} (hs : slot < 6)
    (h : StepRowSem pub R (.wotsChainStep0 layer chain slot) t) :
    (stepAux R t 4 = Goldilocks.zero ∨ stepAux R t 4 = Goldilocks.one) ∧
    (stepAux R t 5 = Goldilocks.zero ∨ stepAux R t 5 = Goldilocks.one) ∧
    (stepAux R t 6 = Goldilocks.zero ∨ stepAux R t 6 = Goldilocks.one) ∧
    stepAux R t 5 *ₚ (Goldilocks.one -ₚ stepAux R t 4) = Goldilocks.zero ∧
    stepAux R t 6 *ₚ (Goldilocks.one -ₚ stepAux R t 5) = Goldilocks.zero ∧
    (stepRegsAt R t).rem.get slot =
      (‹3› -ₚ ((stepAux R t 4 +ₚ stepAux R t 5) +ₚ stepAux R t 6)) +ₚ
        (stepAux R t 7 *ₚ ‹4›) ∧
    (R t).stIn =
      ⟨stepAuxLane R t 0, pub.1.pkSeed,
       stepWotsTweak (stepRegsAt R t) (layer * 2 ^ 44 + chain * 2 ^ 4)⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := (stepRegsAt R t).rem.set slot (stepAux R t 7)
        work := lane4Mux (stepAux R t 4) (stepAuxLane R t 0)
          (lane4Add (stepPermAt R t).b0 (stepAuxLane R t 0))
        acc := stepAux R t 5
        u2 := stepAux R t 6 } := by
  have hG := h.guard
  rcases slot with _ | _ | _ | _ | _ | _ | slot
  all_goals first
    | exact ⟨(stepBoolCheck_eq_zero_iff _).mp (gzz% hG 0),
        (stepBoolCheck_eq_zero_iff _).mp (gzz% hG 1),
        (stepBoolCheck_eq_zero_iff _).mp (gzz% hG 2), gzz% hG 3, gzz% hG 4, gz% hG 5,
        state12_ext12 (gz% hG 6) (gz% hG 8) (gz% hG 10) (gz% hG 12) (gz% hG 7) (gz% hG 9)
          (gz% hG 11) (gz% hG 13) (gz% hG 14) (gz% hG 15) (gz% hG 16) (gz% hG 17), h.regs⟩
    | exact absurd hs (by omega)

theorem stepSem_wotsChainStep2_odd {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain t : Nat} (h : StepRowSem pub R (.wotsChainStep2 layer chain true) t) :
    (R t).stIn =
      ⟨(stepRegsAt R t).work, pub.1.pkSeed,
       stepWotsTweak (stepRegsAt R t) (layer * 2 ^ 44 + chain * 2 ^ 4 + 2)⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        work := lane4Mux (stepRegsAt R t).u2 (stepRegsAt R t).work
          (lane4Add (stepPermAt R t).b0 (stepRegsAt R t).work) } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), h.regs⟩

theorem stepSem_wotsChainStep2_even {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain t : Nat} (h : StepRowSem pub R (.wotsChainStep2 layer chain false) t) :
    (R t).stIn =
      ⟨(stepRegsAt R t).work, pub.1.pkSeed,
       stepWotsTweak (stepRegsAt R t) (layer * 2 ^ 44 + chain * 2 ^ 4 + 2)⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        sub := ⟨lane4Mux (stepRegsAt R t).u2 (stepRegsAt R t).work
            (lane4Add (stepPermAt R t).b0 (stepRegsAt R t).work),
          (stepRegsAt R t).sub.b1, (stepRegsAt R t).sub.b2⟩ } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), h.regs⟩

theorem stepSem_wotsTellPairAbsorb {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {pair t : Nat} (h : StepRowSem pub R (.wotsTellPairAbsorb pair) t) :
    ((pair + 1 == 64) = true → ∀ s < 5, (stepRegsAt R t).rem.get s = Goldilocks.zero) ∧
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepRegsAt R t).sub.b0,
       lane4Add (stepRegsAt R t).main.b1 (stepRegsAt R t).work, (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG : allZeroGoldilocks (stepOpGuardResiduals (.wotsTellPairAbsorb (pair + 1 == 64))
      (Goldilocks.ofNat 0) (stepOpRowInputsPerm pub (R t))) = true := h.guard
  cases hp : (pair + 1 == 64)
  · rw [hp] at hG
    exact ⟨fun hc => absurd hc (by simp),
      state12_ext12 (gz% hG 0) (gz% hG 3) (gz% hG 6) (gz% hG 9) (gz% hG 1) (gz% hG 4)
        (gz% hG 7) (gz% hG 10) (gz% hG 2) (gz% hG 5) (gz% hG 8) (gz% hG 11), h.regs⟩
  · rw [hp] at hG
    refine ⟨fun _ s hs => ?_,
      state12_ext12 (gz% hG 5) (gz% hG 8) (gz% hG 11) (gz% hG 14) (gz% hG 6) (gz% hG 9)
        (gz% hG 12) (gz% hG 15) (gz% hG 7) (gz% hG 10) (gz% hG 13) (gz% hG 16), h.regs⟩
    rcases s with _ | _ | _ | _ | _ | s
    · exact gzz% hG 0
    · exact gzz% hG 1
    · exact gzz% hG 2
    · exact gzz% hG 3
    · exact gzz% hG 4
    · exact absurd hs (by omega)

theorem stepSem_wotsTellFinalSqueeze {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .wotsTellFinalSqueeze t) :
    (R t).stIn = stepSqueezeIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with work := (stepPermAt R t).b0, cursor := (stepRegsAt R t).kp } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), h.regs⟩

theorem stepSem_xmssMerkleBlockA {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer lvl t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockA layer lvl) t) :
    (stepAux R t 0 = Goldilocks.zero ∨ stepAux R t 0 = Goldilocks.one) ∧
    (stepRegsAt R t).cursor = (stepAux R t 0 +ₚ stepAux R t 1) +ₚ stepAux R t 1 ∧
    (R t).stIn =
      ⟨pub.1.pkSeed, lane4MuxL (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2),
       ⟨domainMerkleNode, ‹layer * 2 ^ 48 + (lvl + 1) * 2 ^ 32› +ₚ stepAux R t 1,
        (stepRegsAt R t).treeLo, (stepRegsAt R t).treeHi⟩⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        sub := stepPermAt R t
        work := lane4Mux (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2)
        cursor := stepAux R t 1 } := by
  have hG := h.guard
  exact ⟨(stepBoolCheck_eq_zero_iff _).mp (gzz% hG 0), gz% hG 1,
    state12_ext12 (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 8) (gz% hG 3) (gz% hG 5)
      (gz% hG 7) (gz% hG 9) (gz% hG 10) (gz% hG 11) (gz% hG 12) (gz% hG 13), h.regs⟩

theorem stepSem_xmssMerkleBlockB_inner {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {isTop : Bool} {t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockB false isTop) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with work := (stepPermAt R t).b0 } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), h.regs⟩

theorem stepSem_xmssMerkleBlockB_top {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockB true true) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    (stepRegsAt R t).cursor = Goldilocks.zero ∧
    (stepPermAt R t).b0 = pub.1.pkRoot := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), gzz% hG 12,
    Lane4.ext (gz% hG 13) (gz% hG 14) (gz% hG 15) (gz% hG 16)⟩

theorem stepSem_statefulHmsgBlock0 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statefulHmsgBlock0 t) :
    (∀ i < 6, stepAux R t i = Goldilocks.zero ∨ stepAux R t i = Goldilocks.one) ∧
    (∀ i < 32, stepAux R t (6 + i) = Goldilocks.zero ∨ stepAux R t (6 + i) = Goldilocks.one) ∧
    (R t).stIn =
      ⟨pub.1.pkSeed, pub.1.pkRoot,
       ⟨domainHMsgStateful,
        (stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 6 *ₚ ‹2 ^ 32›) +ₚ
          stepWeightedSum (fun i => stepAux R t (6 + i)) (fun i => 2 ^ i) 32,
        pub.2.limb4, poseidon2IvTag⟩⟩ ∧
    stepRegsAt R (t + 1) =
      { curRoot := pub.1.pkRoot
        kp := stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 6
        treeLo := Goldilocks.zero
        treeHi := Goldilocks.zero
        rem := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
          Goldilocks.zero, Goldilocks.zero⟩
        main := stepPermAt R t
        sub := state12Zero
        work := lane4Zero
        cursor := Goldilocks.zero
        acc := Goldilocks.zero
        u2 := Goldilocks.zero } := by
  have hG := h.guard
  have hA : allZeroGoldilocks ((List.range 6).map
      (fun i => stepBoolCheck (stepAux R t i))) = true := allZero_take hG 6
  have hB : allZeroGoldilocks ((List.range 32).map
      (fun i => stepBoolCheck (stepAux R t (6 + i)))) = true := allZero_take (allZero_drop hG 6) 32
  exact ⟨fun i hi => (stepBoolCheck_eq_zero_iff _).mp ((allZero_map_iff 6 _).mp hA i hi),
    fun i hi => (stepBoolCheck_eq_zero_iff _).mp ((allZero_map_iff 32 _).mp hB i hi),
    state12_ext12 (gz% hG 38) (gz% hG 40) (gz% hG 42) (gz% hG 44) (gz% hG 39) (gz% hG 41)
      (gz% hG 43) (gz% hG 45) (gz% hG 46) (gz% hG 47) (gz% hG 48) (gz% hG 49), h.regs⟩

theorem stepSem_statefulHmsgBlock1 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statefulHmsgBlock1 t) :
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepAuxLane R t 0),
       lane4Add (stepRegsAt R t).main.b1 ⟨pub.2.limb0, pub.2.limb1, pub.2.limb2, pub.2.limb3⟩,
       (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 3) (gz% hG 6) (gz% hG 9) (gz% hG 1) (gz% hG 4)
    (gz% hG 7) (gz% hG 10) (gz% hG 2) (gz% hG 5) (gz% hG 8) (gz% hG 11), h.regs⟩

theorem stepSem_statefulHmsgSqueeze {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statefulHmsgSqueeze t) :
    (R t).stIn = stepSqueezeIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
          Goldilocks.zero, Goldilocks.zero⟩
        main := stepPermAt R t
        acc := Goldilocks.zero } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), h.regs⟩

/-- `HmsgDecompLimb l`: the limb decomposition gate holds, the target sum is checked on the
    last limb, and only `ST_REM_PACK` and the digit accumulator change. -/
theorem stepSem_hmsgDecompLimb {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {l t : Nat} (hl : l < 5) (h : StepRowSem pub R (.hmsgDecompLimb l) t) :
    allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) l) = true ∧
    (l = 4 → stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l stAccOrU1 = ‹192›) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := ⟨stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 7,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 8,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 9,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 10,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 11,
          stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l 12⟩
        acc := stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l stAccOrU1 } := by
  have hG := h.guard
  have hD : allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) l) = true :=
    allZero_take hG 33
  rcases l with _ | _ | _ | _ | _ | l
  · exact ⟨hD, fun hc => absurd hc (by decide), h.regs⟩
  · exact ⟨hD, fun hc => absurd hc (by decide), h.regs⟩
  · exact ⟨hD, fun hc => absurd hc (by decide), h.regs⟩
  · exact ⟨hD, fun hc => absurd hc (by decide), h.regs⟩
  · exact ⟨hD, fun _ => gz% hG 33, h.regs⟩
  · exact absurd hl (by omega)

/-! ### §3.6. WOTS+C chain rows: three guarded rows walk one chain -/

/-- The address registers hold key-pair index `kpN` and the two 32-bit halves of `tree`. -/
structure StepAddrOk (r : StepRegs) (kpN tree : Nat) : Prop where
  kp : r.kp = ‹kpN›
  lo : r.treeLo = ‹tree % 2 ^ 32›
  hi : r.treeHi = ‹(tree / 2 ^ 32) % 2 ^ 32›

/-- Number of skipped chain steps `u0 + u1 + u2` of the `WotsChainStep0` row `t`. -/
def stepChainDigit (R : Nat → StepOpRow) (t : Nat) : Nat :=
  (stepAux R t 4).val + (stepAux R t 5).val + (stepAux R t 6).val

private def stepChainIter (F0 F1 F2 : Lane4 → Lane4) : Nat → Lane4 → Lane4
  | 0, a => F2 (F1 (F0 a))
  | 1, a => F2 (F1 a)
  | 2, a => F2 a
  | _, a => a

private theorem stepChainMux_eq (F0 F1 F2 : Lane4 → Lane4) (u0 u1 u2 : Goldilocks) (a : Lane4)
    (hb0 : u0 = Goldilocks.zero ∨ u0 = Goldilocks.one)
    (hb1 : u1 = Goldilocks.zero ∨ u1 = Goldilocks.one)
    (hb2 : u2 = Goldilocks.zero ∨ u2 = Goldilocks.one)
    (hm1 : u1 *ₚ (Goldilocks.one -ₚ u0) = Goldilocks.zero)
    (hm2 : u2 *ₚ (Goldilocks.one -ₚ u1) = Goldilocks.zero) :
    u0.val + u1.val + u2.val ≤ 3 ∧
    (‹3› -ₚ ((u0 +ₚ u1) +ₚ u2)) = ‹3 - (u0.val + u1.val + u2.val)› ∧
    lane4Mux u2 (lane4Mux u1 (lane4Mux u0 a (F0 a)) (F1 (lane4Mux u0 a (F0 a))))
        (F2 (lane4Mux u1 (lane4Mux u0 a (F0 a)) (F1 (lane4Mux u0 a (F0 a))))) =
      stepChainIter F0 F1 F2 (u0.val + u1.val + u2.val) a := by
  rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl
  all_goals first
    | exact absurd hm1 (by decide +kernel)
    | exact absurd hm2 (by decide +kernel)
    | (refine ⟨by decide, by decide +kernel, ?_⟩
       simp only [lane4Mux_one, lane4Mux_zero]
       rfl)

private theorem stepChainIter_walk (pkSeed : Lane4) (layer tree kpN chain d : Nat) (a : Lane4)
    (hd : d ≤ 3) :
    stepChainIter (fun v => wotsStepHash pkSeed v layer tree kpN chain 0)
        (fun v => wotsStepHash pkSeed v layer tree kpN chain 1)
        (fun v => wotsStepHash pkSeed v layer tree kpN chain 2) d a =
      wotsChainWalk pkSeed layer tree kpN chain d (3 - d) a := by
  rcases d with _ | _ | _ | _ | d
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

private theorem stepWotsHash_eq {R : Nat → StepOpRow} {t : Nat} {r : StepRegs}
    {pkSeed cur : Lane4} {c0 layer chain k kpN tree : Nat}
    (hIn : (R t).stIn = ⟨cur, pkSeed, stepWotsTweak r c0⟩) (hAddr : StepAddrOk r kpN tree)
    (hc0 : c0 = layer * 2 ^ 44 + chain * 2 ^ 4 + k)
    (hl : layer < 64) (hk : kpN < 2 ^ 28) (hc : chain < 4096) (hk16 : k < 16) :
    lane4Add (stepPermAt R t).b0 cur = wotsStepHash pkSeed cur layer tree kpN chain k := by
  have hT : stepWotsTweak r c0 =
      ⟨domainWotsStep, packWotsAddrLimb layer kpN chain k, ‹tree % 2 ^ 32›,
        ‹(tree / 2 ^ 32) % 2 ^ 32›⟩ := by
    unfold stepWotsTweak packWotsAddrLimb
    rw [hAddr.kp, hAddr.lo, hAddr.hi, ← g_ofNat_mul, ← g_ofNat_add, hc0,
      Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hk16]
    have e : layer * 2 ^ 44 + chain * 2 ^ 4 + k + kpN * 2 ^ 16 =
        layer * 2 ^ 44 + kpN * 2 ^ 16 + chain * 16 + k := by omega
    rw [e]
  unfold stepPermAt wotsStepHash poseidon2Compress12FF
  rw [hIn, hT]

/-- **Chain rows.** The three rows of one WOTS+C chain shift the remaining-step count
    `3 - d` out of the chain's `ST_REM_PACK` limb and leave `wotsChainWalk` of the signature
    value from step `d` in `ST_WORK` (odd chain) or `ST_SUB_SPONGE[0..4]` (even chain). -/
theorem stepChain_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer chain slot t kpN tree : Nat} {odd : Bool}
    (h0 : StepRowSem pub R (.wotsChainStep0 layer chain slot) t)
    (h1 : StepRowSem pub R (.wotsChainStep1 layer chain) (t + 1))
    (h2 : StepRowSem pub R (.wotsChainStep2 layer chain odd) (t + 2))
    (hs : slot < 6) (hAddr : StepAddrOk (stepRegsAt R t) kpN tree)
    (hl : layer < 64) (hk : kpN < 2 ^ 28) (hc : chain < 4096) :
    stepChainDigit R t ≤ 3 ∧
    (stepRegsAt R t).rem.get slot =
      ‹3 - stepChainDigit R t› +ₚ (stepAux R t 7 *ₚ ‹4›) ∧
    ∃ (W : Lane4) (A U : Goldilocks), stepRegsAt R (t + 3) =
      { stepRegsAt R t with
        rem := (stepRegsAt R t).rem.set slot (stepAux R t 7)
        sub := if odd then (stepRegsAt R t).sub else
          ⟨wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
              (3 - stepChainDigit R t) (stepAuxLane R t 0),
            (stepRegsAt R t).sub.b1, (stepRegsAt R t).sub.b2⟩
        work := if odd then
            wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
              (3 - stepChainDigit R t) (stepAuxLane R t 0)
          else W
        acc := A
        u2 := U } := by
  obtain ⟨hb0, hb1, hb2, hm1, hm2, hRem, hIn0, hR1⟩ := stepSem_wotsChainStep0 hs h0
  obtain ⟨hIn1, hR2⟩ := stepSem_wotsChainStep1 h1
  have hR2' : stepRegsAt R (t + 2) = _ := hR2
  have hA1 : StepAddrOk (stepRegsAt R (t + 1)) kpN tree := by
    rw [hR1]; exact ⟨hAddr.kp, hAddr.lo, hAddr.hi⟩
  have hA2 : StepAddrOk (stepRegsAt R (t + 2)) kpN tree := by
    rw [hR2']; exact ⟨hA1.kp, hA1.lo, hA1.hi⟩
  have e0 := stepWotsHash_eq (k := 0) (c0 := layer * 2 ^ 44 + chain * 2 ^ 4) hIn0 hAddr
    (Nat.add_zero _).symm hl hk hc (by decide)
  have e1 := stepWotsHash_eq (k := 1) (c0 := layer * 2 ^ 44 + chain * 2 ^ 4 + 1) hIn1 hA1
    (Eq.refl _) hl hk hc (by decide)
  have hw1 : (stepRegsAt R (t + 1)).work =
      lane4Mux (stepAux R t 4) (stepAuxLane R t 0)
        (wotsStepHash pub.1.pkSeed (stepAuxLane R t 0) layer tree kpN chain 0) := by
    rw [hR1, ← e0]
  have hacc1 : (stepRegsAt R (t + 1)).acc = stepAux R t 5 := by rw [hR1]
  have hu1 : (stepRegsAt R (t + 1)).u2 = stepAux R t 6 := by rw [hR1]
  have hw2 : (stepRegsAt R (t + 2)).work =
      lane4Mux (stepAux R t 5)
        (lane4Mux (stepAux R t 4) (stepAuxLane R t 0)
          (wotsStepHash pub.1.pkSeed (stepAuxLane R t 0) layer tree kpN chain 0))
        (wotsStepHash pub.1.pkSeed
          (lane4Mux (stepAux R t 4) (stepAuxLane R t 0)
            (wotsStepHash pub.1.pkSeed (stepAuxLane R t 0) layer tree kpN chain 0))
          layer tree kpN chain 1) := by
    rw [hR2']
    show lane4Mux (stepRegsAt R (t + 1)).acc (stepRegsAt R (t + 1)).work
      (lane4Add (stepPermAt R (t + 1)).b0 (stepRegsAt R (t + 1)).work) = _
    rw [e1, hacc1, hw1]
  have hu2 : (stepRegsAt R (t + 2)).u2 = stepAux R t 6 := by
    rw [hR2']; exact hu1
  obtain ⟨hd, hThree, hIter⟩ := stepChainMux_eq
    (fun v => wotsStepHash pub.1.pkSeed v layer tree kpN chain 0)
    (fun v => wotsStepHash pub.1.pkSeed v layer tree kpN chain 1)
    (fun v => wotsStepHash pub.1.pkSeed v layer tree kpN chain 2)
    (stepAux R t 4) (stepAux R t 5) (stepAux R t 6) (stepAuxLane R t 0) hb0 hb1 hb2 hm1 hm2
  have hWalk := stepChainIter_walk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
    (stepAuxLane R t 0) hd
  refine ⟨hd, ?_, (stepRegsAt R (t + 2)).work, (stepRegsAt R (t + 2)).acc,
    (stepRegsAt R (t + 2)).u2, ?_⟩
  · rw [hRem, hThree]
    rfl
  · cases odd
    · obtain ⟨hIn2, hR3⟩ := stepSem_wotsChainStep2_even h2
      have hR3' : stepRegsAt R (t + 3) = _ := hR3
      have e2 := stepWotsHash_eq (k := 2) (c0 := layer * 2 ^ 44 + chain * 2 ^ 4 + 2) hIn2 hA2
        (Eq.refl _) hl hk hc (by decide)
      have hX : lane4Mux (stepRegsAt R (t + 2)).u2 (stepRegsAt R (t + 2)).work
          (lane4Add (stepPermAt R (t + 2)).b0 (stepRegsAt R (t + 2)).work) =
          wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
            (3 - stepChainDigit R t) (stepAuxLane R t 0) := by
        rw [e2, hu2, hw2, ← hWalk]
        exact hIter
      rw [hR3', hX, hR2', hR1]
      rfl
    · obtain ⟨hIn2, hR3⟩ := stepSem_wotsChainStep2_odd h2
      have hR3' : stepRegsAt R (t + 3) = _ := hR3
      have e2 := stepWotsHash_eq (k := 2) (c0 := layer * 2 ^ 44 + chain * 2 ^ 4 + 2) hIn2 hA2
        (Eq.refl _) hl hk hc (by decide)
      have hX : lane4Mux (stepRegsAt R (t + 2)).u2 (stepRegsAt R (t + 2)).work
          (lane4Add (stepPermAt R (t + 2)).b0 (stepRegsAt R (t + 2)).work) =
          wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
            (3 - stepChainDigit R t) (stepAuxLane R t 0) := by
        rw [e2, hu2, hw2, ← hWalk]
        exact hIter
      rw [hR3', hX, hR2', hR1]
      rfl

/-! ### §3.7. One chain pair: two chains and their sponge absorption -/

/-- The seven opcodes of chain pair `pair` of a WOTS+C layer. -/
def stepPairOps (layer pair : Nat) : List StepOp :=
  (List.range 2).flatMap (fun sub =>
      [StepOp.wotsChainStep0 layer (2 * pair + sub) (wotsPackSlot (2 * pair + sub)),
       StepOp.wotsChainStep1 layer (2 * pair + sub),
       StepOp.wotsChainStep2 layer (2 * pair + sub) (sub == 1)]) ++
    [StepOp.wotsTellPairAbsorb pair]

/-- Endpoint recovered by the chain whose `WotsChainStep0` row is `t`. -/
def stepChainEndpoint (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (layer tree kpN chain t : Nat) : Lane4 :=
  wotsChainWalk pub.1.pkSeed layer tree kpN chain (stepChainDigit R t)
    (3 - stepChainDigit R t) (stepAuxLane R t 0)

/-- What the seven rows of one chain pair starting at row `T` establish. -/
structure StepPairFacts (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (layer kpN tree pair T : Nat) : Prop where
  dE : stepChainDigit R T ≤ 3
  dO : stepChainDigit R (T + 3) ≤ 3
  getE : (stepRegsAt R T).rem.get (wotsPackSlot (2 * pair)) =
    ‹3 - stepChainDigit R T› +ₚ (stepAux R T 7 *ₚ ‹4›)
  setE : (stepRegsAt R (T + 3)).rem =
    (stepRegsAt R T).rem.set (wotsPackSlot (2 * pair)) (stepAux R T 7)
  getO : (stepRegsAt R (T + 3)).rem.get (wotsPackSlot (2 * pair + 1)) =
    ‹3 - stepChainDigit R (T + 3)› +ₚ (stepAux R (T + 3) 7 *ₚ ‹4›)
  setO : (stepRegsAt R (T + 7)).rem =
    (stepRegsAt R (T + 3)).rem.set (wotsPackSlot (2 * pair + 1)) (stepAux R (T + 3) 7)
  zero : (pair + 1 == 64) = true → ∀ s < 5, (stepRegsAt R (T + 7)).rem.get s = Goldilocks.zero
  main : (stepRegsAt R (T + 7)).main =
    poseidon2Perm12
      ⟨lane4Add (stepRegsAt R T).main.b0 (stepChainEndpoint pub R layer tree kpN (2 * pair) T),
       lane4Add (stepRegsAt R T).main.b1
         (stepChainEndpoint pub R layer tree kpN (2 * pair + 1) (T + 3)),
       (stepRegsAt R T).main.b2⟩
  curRoot : (stepRegsAt R (T + 7)).curRoot = (stepRegsAt R T).curRoot
  kp : (stepRegsAt R (T + 7)).kp = (stepRegsAt R T).kp
  treeLo : (stepRegsAt R (T + 7)).treeLo = (stepRegsAt R T).treeLo
  treeHi : (stepRegsAt R (T + 7)).treeHi = (stepRegsAt R T).treeHi

theorem stepPair_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer pair T kpN tree : Nat}
    (hRun : StepRunAt pub R (stepPairOps layer pair) T)
    (hAddr : StepAddrOk (stepRegsAt R T) kpN tree)
    (hl : layer < 64) (hk : kpN < 2 ^ 28) (hp : pair < 64) :
    StepPairFacts pub R layer kpN tree pair T := by
  have h0 : StepRowSem pub R (.wotsChainStep0 layer (2 * pair) (wotsPackSlot (2 * pair))) T :=
    hRun 0 (Nat.le_of_ble_eq_true rfl)
  have h1 : StepRowSem pub R (.wotsChainStep1 layer (2 * pair)) (T + 1) :=
    hRun 1 (Nat.le_of_ble_eq_true rfl)
  have h2 : StepRowSem pub R (.wotsChainStep2 layer (2 * pair) false) (T + 2) :=
    hRun 2 (Nat.le_of_ble_eq_true rfl)
  have h3 : StepRowSem pub R
      (.wotsChainStep0 layer (2 * pair + 1) (wotsPackSlot (2 * pair + 1))) (T + 3) :=
    hRun 3 (Nat.le_of_ble_eq_true rfl)
  have h4 : StepRowSem pub R (.wotsChainStep1 layer (2 * pair + 1)) (T + 3 + 1) :=
    hRun 4 (Nat.le_of_ble_eq_true rfl)
  have h5 : StepRowSem pub R (.wotsChainStep2 layer (2 * pair + 1) true) (T + 3 + 2) :=
    hRun 5 (Nat.le_of_ble_eq_true rfl)
  have h6 : StepRowSem pub R (.wotsTellPairAbsorb pair) (T + 6) :=
    hRun 6 (Nat.le_of_ble_eq_true rfl)
  have hsE : wotsPackSlot (2 * pair) < 6 := Nat.lt_succ_of_lt (wotsPackSlot_lt_5 _)
  have hsO : wotsPackSlot (2 * pair + 1) < 6 := Nat.lt_succ_of_lt (wotsPackSlot_lt_5 _)
  obtain ⟨hdE, hgE, WE, AE, UE, hR3⟩ :=
    stepChain_sem (odd := false) h0 h1 h2 hsE hAddr hl hk (by omega)
  have hA3 : StepAddrOk (stepRegsAt R (T + 3)) kpN tree := by
    rw [hR3]; exact ⟨hAddr.kp, hAddr.lo, hAddr.hi⟩
  obtain ⟨hdO, hgO, WO, AO, UO, hR6⟩ :=
    stepChain_sem (odd := true) h3 h4 h5 hsO hA3 hl hk (by omega)
  have hR6' : stepRegsAt R (T + 6) = _ := hR6
  obtain ⟨hZero, hIn, hR7⟩ := stepSem_wotsTellPairAbsorb h6
  have hR7' : stepRegsAt R (T + 7) = _ := hR7
  refine
    { dE := hdE, dO := hdO, getE := hgE, setE := by rw [hR3], getO := hgO
      setO := by rw [hR7', hR6'], zero := ?_, main := ?_, curRoot := by rw [hR7', hR6', hR3]
      kp := by rw [hR7', hR6', hR3], treeLo := by rw [hR7', hR6', hR3]
      treeHi := by rw [hR7', hR6', hR3] }
  · intro hc s hs
    rw [hR7']
    exact hZero hc s hs
  · rw [hR7']
    show stepPermAt R (T + 6) = _
    unfold stepPermAt stepChainEndpoint
    rw [hIn, hR6', hR3]
    rfl

/-! ### §3.8. `ST_REM_PACK` bookkeeping: the chain rows unpack exactly the packed digits -/

/-- A run of rows owning one `ST_REM_PACK` limb unpacks that limb digit by digit in base `B`;
    since the limb ends at zero and `B ^ len < p`, the limb value is the base-`B` number of
    the digits. -/
private theorem stepRemSlot_digits (g : Nat → StepRem) (B : Nat) (hB : 0 < B) (dig : Nat → Nat)
    (x : Nat → Goldilocks) (slotOf : Nat → Nat) (N : Nat)
    (hd : ∀ c < N, dig c < B)
    (hget : ∀ c < N, (g c).get (slotOf c) = ‹dig c› +ₚ (x c *ₚ ‹B›))
    (hset : ∀ c < N, g (c + 1) = (g c).set (slotOf c) (x c))
    (hslot : ∀ c < N, slotOf c < 6)
    (s a len : Nat)
    (hRange : ∀ c < N, slotOf c = s ↔ a ≤ c ∧ c < a + len)
    (haN : a + len ≤ N) (hEnd : (g N).get s = Goldilocks.zero)
    (hLen : B ^ len < goldilocksPrime) :
    ((g 0).get s).val = evalBaseDigits B ((List.range' a len).map dig) := by
  have hStep : ∀ c < N, slotOf c ≠ s → (g (c + 1)).get s = (g c).get s := by
    intro c hc hne
    rw [hset c hc, StepRem.get_set _ _ _ _ (hslot c hc),
      ite_eq_right_of_eq_false _ _ (eq_false (fun h => hne h.symm))]
  have hStepS : ∀ c < N, slotOf c = s → (g (c + 1)).get s = x c := by
    intro c hc he
    rw [hset c hc, StepRem.get_set _ _ _ _ (hslot c hc),
      ite_eq_left_of_eq_true _ _ (eq_true he.symm)]
  have hCarry1 : ∀ c, c ≤ a → (g c).get s = (g 0).get s := by
    intro c
    induction c with
    | zero => intro _; rfl
    | succ c ih =>
      intro hc
      have hcN : c < N := by omega
      rw [hStep c hcN (fun h => by have := (hRange c hcN).mp h; omega)]
      exact ih (by omega)
  have hCarry2 : ∀ k, a + len + k ≤ N → (g (a + len + k)).get s = (g (a + len)).get s := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hcN : a + len + k < N := by omega
      have e : a + len + (k + 1) = a + len + k + 1 := by omega
      rw [e, hStep _ hcN (fun h => by have := (hRange _ hcN).mp h; omega)]
      exact ih (by omega)
  have hChain : ∀ n b, a ≤ b → b + n ≤ a + len →
      UnpackChain B ((g b).get s) ((List.range' b n).map dig) ((g (b + n)).get s) := by
    intro n
    induction n with
    | zero => intro b _ _; exact rfl
    | succ n ih =>
      intro b hab hbn
      have hbN : b < N := by omega
      have hsb : slotOf b = s := (hRange b hbN).mpr ⟨hab, by omega⟩
      refine ⟨hd b hbN, (g (b + 1)).get s, ?_, ?_⟩
      · have h1 := hget b hbN
        rw [hsb] at h1
        rw [h1, hStepS b hbN hsb]
      · have e : b + (n + 1) = b + 1 + n := by omega
        rw [e]
        exact ih (b + 1) (by omega) (by omega)
  have hC := hChain len a (Nat.le_refl a) (Nat.le_refl _)
  have hZ : (g (a + len)).get s = Goldilocks.zero := by
    have h2 := hCarry2 (N - (a + len)) (by omega)
    have e : a + len + (N - (a + len)) = N := by omega
    rw [e, hEnd] at h2
    exact h2.symm
  rw [hZ, hCarry1 a (Nat.le_refl a)] at hC
  have hLen' : B ^ ((List.range' a len).map dig).length < goldilocksPrime := by
    rw [List.length_map, List.length_range']
    exact hLen
  exact (baseBUnpackChain_backward B hB _ _ hLen' hC).1

/-- Absorbing an even-length list of digests followed by one more pair applies the two-block
    permutation step once more. -/
private theorem absorbPairsPoly_append_pair {Dg S : Type} (perm1 : S → Dg → S)
    (perm2 : S → Dg → Dg → S) (e0 e1 : Dg) :
    ∀ (xs : List Dg) (st : S), xs.length % 2 = 0 →
      absorbPairsPoly perm1 perm2 (xs ++ [e0, e1]) st none =
        perm2 (absorbPairsPoly perm1 perm2 xs st none) e0 e1
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | x :: y :: rest, st, h => by
    have hr : rest.length % 2 = 0 := by
      simp only [List.length_cons] at h
      omega
    exact absorbPairsPoly_append_pair perm1 perm2 e0 e1 rest (perm2 st x y) hr

/-! ### §3.9. The WOTS+C part of one layer -/

/-- Row of the `WotsChainStep0` of chain `c` in a layer whose `WotsTellInit` row is `t0`. -/
def stepChainRow (t0 c : Nat) : Nat := t0 + 1 + 7 * (c / 2) + 3 * (c % 2)

/-- The WOTS+C part of a layer: `WotsTellInit`, 64 chain pairs, `WotsTellFinalSqueeze`. -/
def stepWotsOps (layer : Nat) : List StepOp :=
  [StepOp.wotsTellInit layer] ++ (List.range 64).flatMap (stepPairOps layer) ++
    [StepOp.wotsTellFinalSqueeze]

/-- The 128 chain endpoints recovered by the rows of a layer starting at row `t0`. -/
def stepLayerEndpoints (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (layer tree kpN t0 : Nat) : List Lane4 :=
  (List.range 128).map fun c => stepChainEndpoint pub R layer tree kpN c (stepChainRow t0 c)

/-- **WOTS+C layer rows.** The 450 rows `WotsTellInit .. WotsTellFinalSqueeze` of a layer
    leave in `ST_WORK` the `T_ell` sponge of the 128 walked chain endpoints, and every
    `ST_REM_PACK` limb entering the layer is the base-4 number of the remaining-step counts
    `3 - d_c` of the chains it owns. -/
theorem stepWots_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer t0 kpN tree : Nat}
    (hRun : StepRunAt pub R (stepWotsOps layer) t0)
    (hAddr : StepAddrOk (stepRegsAt R t0) kpN tree) (hl : layer < 64) (hk : kpN < 2 ^ 28) :
    (∀ c < 128, stepChainDigit R (stepChainRow t0 c) ≤ 3) ∧
    (∀ s a len : Nat, (∀ c < 128, wotsPackSlot c = s ↔ a ≤ c ∧ c < a + len) → s < 5 →
      a + len ≤ 128 → 4 ^ len < goldilocksPrime →
      ((stepRegsAt R t0).rem.get s).val =
        evalBaseDigits 4 ((List.range' a len).map
          (fun c => 3 - stepChainDigit R (stepChainRow t0 c)))) ∧
    (stepRegsAt R (t0 + 450)).work =
      compressWotsEndpointsSponge pub.1.pkSeed layer tree kpN
        (stepLayerEndpoints pub R layer tree kpN t0) ∧
    (stepRegsAt R (t0 + 450)).curRoot = (stepRegsAt R t0).curRoot ∧
    StepAddrOk (stepRegsAt R (t0 + 450)) kpN tree ∧
    (stepRegsAt R (t0 + 450)).cursor = ‹kpN› := by
  have hInit : StepRowSem pub R (.wotsTellInit layer) t0 := hRun.append_left.append_left.head
  have hPairs : StepRunAt pub R ((List.range 64).flatMap (stepPairOps layer)) (t0 + 1) :=
    hRun.append_left.append_right
  have hPair : ∀ p < 64, StepRunAt pub R (stepPairOps layer p) (t0 + 1 + p * 7) :=
    StepRunAt.flatMap_range (L := 7) (fun _ => rfl) 64 hPairs
  have hlen : ([StepOp.wotsTellInit layer] ++
      (List.range 64).flatMap (stepPairOps layer)).length = 449 := by
    rw [List.length_append, flatMap_range_uniform_length _ 7 (fun _ => rfl)]
    rfl
  have hSq : StepRowSem pub R .wotsTellFinalSqueeze (t0 + 449) := by
    have h := hRun.append_right
    rw [hlen] at h
    exact h.head
  obtain ⟨hInInit, hR1⟩ := stepSem_wotsTellInit hInit
  have hFrame : ∀ p, p ≤ 64 →
      (stepRegsAt R (t0 + 1 + p * 7)).kp = (stepRegsAt R t0).kp ∧
      (stepRegsAt R (t0 + 1 + p * 7)).treeLo = (stepRegsAt R t0).treeLo ∧
      (stepRegsAt R (t0 + 1 + p * 7)).treeHi = (stepRegsAt R t0).treeHi ∧
      (stepRegsAt R (t0 + 1 + p * 7)).curRoot = (stepRegsAt R t0).curRoot := by
    intro p
    induction p with
    | zero =>
      intro _
      have h0 : stepRegsAt R (t0 + 1 + 0 * 7) = _ := hR1
      rw [h0]
      exact ⟨rfl, rfl, rfl, rfl⟩
    | succ p ih =>
      intro hp
      obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
      have hA : StepAddrOk (stepRegsAt R (t0 + 1 + p * 7)) kpN tree :=
        ⟨i1.trans hAddr.kp, i2.trans hAddr.lo, i3.trans hAddr.hi⟩
      have F := stepPair_sem (hPair p (by omega)) hA hl hk (by omega)
      have e : t0 + 1 + (p + 1) * 7 = t0 + 1 + p * 7 + 7 := by omega
      rw [e]
      exact ⟨F.kp.trans i1, F.treeLo.trans i2, F.treeHi.trans i3, F.curRoot.trans i4⟩
  have hF : ∀ p, p < 64 → StepPairFacts pub R layer kpN tree p (t0 + 1 + p * 7) := by
    intro p hp
    obtain ⟨i1, i2, i3, _⟩ := hFrame p (by omega)
    exact stepPair_sem (hPair p hp)
      ⟨i1.trans hAddr.kp, i2.trans hAddr.lo, i3.trans hAddr.hi⟩ hl hk hp
  have rowE : ∀ p, stepChainRow t0 (2 * p) = t0 + 1 + p * 7 := by
    intro p; unfold stepChainRow; omega
  have rowO : ∀ p, stepChainRow t0 (2 * p + 1) = t0 + 1 + p * 7 + 3 := by
    intro p; unfold stepChainRow; omega
  have rowN : ∀ p, stepChainRow t0 (2 * p + 1 + 1) = t0 + 1 + p * 7 + 7 := by
    intro p; unfold stepChainRow; omega
  have hSplit : ∀ c, c < 128 → ∃ p, p < 64 ∧ (c = 2 * p ∨ c = 2 * p + 1) :=
    fun c hc => ⟨c / 2, by omega, by omega⟩
  have hd : ∀ c < 128, stepChainDigit R (stepChainRow t0 c) ≤ 3 := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE]; exact (hF p hp).dE
    · rw [rowO]; exact (hF p hp).dO
  have hget : ∀ c < 128, ((stepRegsAt R (stepChainRow t0 c)).rem).get (wotsPackSlot c) =
      ‹3 - stepChainDigit R (stepChainRow t0 c)› +ₚ (stepAux R (stepChainRow t0 c) 7 *ₚ ‹4›) := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE]; exact (hF p hp).getE
    · rw [rowO]; exact (hF p hp).getO
  have hset : ∀ c < 128, (stepRegsAt R (stepChainRow t0 (c + 1))).rem =
      ((stepRegsAt R (stepChainRow t0 c)).rem).set (wotsPackSlot c)
        (stepAux R (stepChainRow t0 c) 7) := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE, rowO]; exact (hF p hp).setE
    · rw [rowO, rowN]; exact (hF p hp).setO
  have hEnd : ∀ s < 5, ((stepRegsAt R (stepChainRow t0 128)).rem).get s = Goldilocks.zero := by
    intro s hs
    have e : stepChainRow t0 128 = t0 + 1 + 63 * 7 + 7 := by unfold stepChainRow; omega
    rw [e]
    exact (hF 63 (by decide)).zero rfl s hs
  have hG0 : (stepRegsAt R (stepChainRow t0 0)).rem = (stepRegsAt R t0).rem := by
    have e : stepChainRow t0 0 = t0 + 1 := by unfold stepChainRow; omega
    rw [e, hR1]
  have hMain : ∀ p, p ≤ 64 → (stepRegsAt R (t0 + 1 + p * 7)).main =
      absorbDigest4Pairs (stepPermAt R t0)
        ((List.range (2 * p)).map fun c =>
          stepChainEndpoint pub R layer tree kpN c (stepChainRow t0 c)) := by
    intro p
    induction p with
    | zero =>
      intro _
      have h0 : stepRegsAt R (t0 + 1 + 0 * 7) = _ := hR1
      rw [h0]
      rfl
    | succ p ih =>
      intro hp
      have F := hF p (by omega)
      have e : t0 + 1 + (p + 1) * 7 = t0 + 1 + p * 7 + 7 := by omega
      have e2 : 2 * (p + 1) = 2 * p + 1 + 1 := by omega
      rw [e, F.main, ih (by omega), e2, List.range_succ, List.range_succ, List.append_assoc,
        List.map_append]
      unfold absorbDigest4Pairs
      have hEven : ((List.range (2 * p)).map fun c =>
          stepChainEndpoint pub R layer tree kpN c (stepChainRow t0 c)).length % 2 = 0 := by
        rw [List.length_map, List.length_range]
        omega
      have hApp := absorbPairsPoly_append_pair
        (fun (s : Poseidon2State12) (e0 : Lane4) =>
          poseidon2Perm12 ⟨lane4Add s.b0 e0, s.b1, s.b2⟩)
        (fun (s : Poseidon2State12) (e0 e1 : Lane4) =>
          poseidon2Perm12 ⟨lane4Add s.b0 e0, lane4Add s.b1 e1, s.b2⟩)
        (stepChainEndpoint pub R layer tree kpN (2 * p) (stepChainRow t0 (2 * p)))
        (stepChainEndpoint pub R layer tree kpN (2 * p + 1) (stepChainRow t0 (2 * p + 1)))
        _ (stepPermAt R t0) hEven
      rw [rowE, rowO] at hApp
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
      rw [rowE, rowO]
      exact hApp.symm
  obtain ⟨hInSq, hR450⟩ := stepSem_wotsTellFinalSqueeze hSq
  have hR450' : stepRegsAt R (t0 + 450) = _ := hR450
  obtain ⟨f1, f2, f3, f4⟩ := hFrame 64 (Nat.le_refl _)
  have e64 : t0 + 1 + 64 * 7 = t0 + 449 := by omega
  rw [e64] at f1 f2 f3 f4
  have hM64 := hMain 64 (Nat.le_refl _)
  rw [e64] at hM64
  refine ⟨hd, ?_, ?_, ?_, ?_, ?_⟩
  · intro s a len hRange hs haN hLen
    have h := stepRemSlot_digits
      (fun c => (stepRegsAt R (stepChainRow t0 c)).rem) 4 (by decide)
      (fun c => 3 - stepChainDigit R (stepChainRow t0 c))
      (fun c => stepAux R (stepChainRow t0 c) 7) wotsPackSlot 128
      (fun c hc => by have := hd c hc; show 3 - _ < 4; omega) hget hset
      (fun c _ => Nat.lt_succ_of_lt (wotsPackSlot_lt_5 c)) s a len hRange haN (hEnd s hs) hLen
    rw [← hG0]
    exact h
  · have hInit' : (R t0).stIn =
        ⟨pub.1.pkSeed,
         ⟨‹(layer % 2 ^ 32) * 2 ^ 32 + kpN % 2 ^ 32›, ‹tree % 2 ^ 32›,
          ‹(tree / 2 ^ 32) % 2 ^ 32›, ‹128›⟩,
         ⟨domainWotsPk, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩ := by
      rw [hInInit, hAddr.kp, hAddr.lo, hAddr.hi, ← g_ofNat_add,
        Nat.mod_eq_of_lt (by omega : layer < 2 ^ 32), Nat.mod_eq_of_lt (by omega : kpN < 2 ^ 32)]
    rw [hR450']
    show (stepPermAt R (t0 + 449)).b0 = _
    unfold stepPermAt
    rw [hInSq]
    unfold stepSqueezeIn
    rw [hM64]
    unfold stepPermAt compressWotsEndpointsSponge stepLayerEndpoints
    rw [hInit', List.length_map, List.length_range]
  · rw [hR450']; exact f4
  · rw [hR450']
    exact ⟨f1.trans hAddr.kp, f2.trans hAddr.lo, f3.trans hAddr.hi⟩
  · rw [hR450']
    exact f1.trans hAddr.kp

/-! ### §3.10. The subtree Merkle path of one layer -/

/-- The Merkle part of a layer: per level one `XmssMerkleBlockA` and one `XmssMerkleBlockB`. -/
def stepMerkleOps (layer subHeight : Nat) (isTopFinal : Bool) : List StepOp :=
  (List.range subHeight).flatMap (fun lvl =>
    [StepOp.xmssMerkleBlockA layer lvl,
     StepOp.xmssMerkleBlockB (lvl + 1 == subHeight) ((lvl + 1 == subHeight) && isTopFinal)])

theorem pushLayerWotsAndMerkle_eq (layer subHeight : Nat) (isTopFinal : Bool) :
    pushLayerWotsAndMerkle layer subHeight isTopFinal =
      stepWotsOps layer ++ stepMerkleOps layer subHeight isTopFinal := by
  rfl

/-- The 2-block node sponge with its address limbs given as field elements. -/
def stepNodeHashF (domainTag meta0 treeLo treeHi : Goldilocks) (pkSeed left right : Lane4) :
    Lane4 :=
  (poseidon2Perm12
    ⟨lane4Add (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b0 right,
     ⟨(poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b1.x0 +ₚ Goldilocks.one,
      (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b1.x1 +ₚ poseidon2IvTag,
      (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b1.x2,
      (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b1.x3⟩,
     (poseidon2Perm12 ⟨pkSeed, left, ⟨domainTag, meta0, treeLo, treeHi⟩⟩).b2⟩).b0

/-- Agreement of two register files outside `ST_SUB_SPONGE`, `ST_WORK`, `ST_CURSOR_IDX` and
    the two chain-step flags. -/
structure StepFrameSWC (a b : StepRegs) : Prop where
  curRoot : a.curRoot = b.curRoot
  kp : a.kp = b.kp
  treeLo : a.treeLo = b.treeLo
  treeHi : a.treeHi = b.treeHi
  rem : a.rem = b.rem
  main : a.main = b.main

/-- A Merkle `BlockA` row with domain tag `tag` and node address limb `pre + aux[1]`. -/
structure StepMerkleARow (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow) (t : Nat)
    (tag pre : Goldilocks) : Prop where
  bit : stepAux R t 0 = Goldilocks.zero ∨ stepAux R t 0 = Goldilocks.one
  cur : (stepRegsAt R t).cursor = (stepAux R t 0 +ₚ stepAux R t 1) +ₚ stepAux R t 1
  stIn : (R t).stIn =
    ⟨pub.1.pkSeed, lane4MuxL (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2),
     ⟨tag, pre +ₚ stepAux R t 1, (stepRegsAt R t).treeLo, (stepRegsAt R t).treeHi⟩⟩
  next : stepRegsAt R (t + 1) =
    { stepRegsAt R t with
      sub := stepPermAt R t
      work := lane4Mux (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2)
      cursor := stepAux R t 1 }

theorem stepMerkleARow_xmss {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer lvl t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockA layer lvl) t) :
    StepMerkleARow pub R t domainMerkleNode ‹layer * 2 ^ 48 + (lvl + 1) * 2 ^ 32› :=
  match stepSem_xmssMerkleBlockA h with
  | ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩

/-- One Merkle level: the `BlockA` row followed by a row whose `st_in` is the second block
    computes the 2-block node sponge of the selected `(left, right)` pair. -/
theorem stepMerkleLevel_hash {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {tag pre : Goldilocks} {t : Nat} (hA : StepMerkleARow pub R t tag pre)
    (hInB : (R (t + 1)).stIn = stepMerkleBIn (stepRegsAt R (t + 1))) :
    (stepPermAt R (t + 1)).b0 =
      stepNodeHashF tag (pre +ₚ stepAux R t 1)
        (stepRegsAt R t).treeLo (stepRegsAt R t).treeHi pub.1.pkSeed
        (lane4MuxL (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2))
        (lane4Mux (stepAux R t 0) (stepRegsAt R t).work (stepAuxLane R t 2)) := by
  unfold stepPermAt
  rw [hInB]
  unfold stepMerkleBIn
  rw [hA.next]
  show (poseidon2Perm12 _).b0 = _
  unfold stepPermAt stepNodeHashF
  rw [hA.stIn]

/-- A halving chain `X l = bit l + 2 * X (l + 1)` ending at zero determines every `X l` and
    every bit from `X 0`. -/
private theorem stepHalving_chain (X : Nat → Goldilocks) (bit : Nat → Nat) (h : Nat)
    (hStep : ∀ l < h, bit l < 2 ∧ X l = ‹bit l› +ₚ (X (l + 1) *ₚ ‹2›))
    (hEnd : X h = Goldilocks.zero) (hPow : 2 ^ h < goldilocksPrime) :
    (X 0).val < 2 ^ h ∧
    ∀ l, l ≤ h → (X l).val = (X 0).val / 2 ^ l ∧ (l < h → bit l = ((X 0).val / 2 ^ l) % 2) := by
  have hChain : ∀ n l, l + n = h →
      UnpackChain 2 (X l) ((List.range' l n).map bit) Goldilocks.zero := by
    intro n
    induction n with
    | zero =>
      intro l hl
      have e : l = h := by omega
      rw [e]
      exact hEnd
    | succ n ih =>
      intro l hl
      have hs := hStep l (by omega)
      exact ⟨hs.1, X (l + 1), hs.2, ih (l + 1) (by omega)⟩
  have hVal : ∀ l, l ≤ h →
      (X l).val = evalBaseDigits 2 ((List.range' l (h - l)).map bit) ∧ (X l).val < 2 ^ (h - l) := by
    intro l hl
    have hLen : 2 ^ ((List.range' l (h - l)).map bit).length < goldilocksPrime := by
      rw [List.length_map, List.length_range']
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (Nat.sub_le h l)) hPow
    have hB := baseBUnpackChain_backward 2 (by decide) _ (X l) hLen (hChain (h - l) l (by omega))
    refine ⟨hB.1, ?_⟩
    have h2 := hB.2.1
    rw [List.length_map, List.length_range'] at h2
    exact h2
  have hRel : ∀ l, l < h → (X l).val = bit l + 2 * (X (l + 1)).val := by
    intro l hl
    have e : h - l = (h - (l + 1)) + 1 := by omega
    have h1 := (hVal l (by omega)).1
    rw [e] at h1
    rw [h1, (hVal (l + 1) (by omega)).1]
    rfl
  have hDiv : ∀ l, l ≤ h → (X l).val = (X 0).val / 2 ^ l := by
    intro l
    induction l with
    | zero => intro _; rw [Nat.pow_zero, Nat.div_one]
    | succ l ih =>
      intro hl
      have hr := hRel l (by omega)
      have hb := (hStep l (by omega)).1
      have ih' := ih (by omega)
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← ih']
      omega
  refine ⟨?_, fun l hl => ⟨hDiv l hl, fun hlt => ?_⟩⟩
  · have h0 := (hVal 0 (Nat.zero_le _)).2
    rw [Nat.sub_zero] at h0
    exact h0
  · have hr := hRel l hlt
    have hb := (hStep l hlt).1
    rw [← hDiv l hl]
    omega

/-- Folding per-level parents along an authentication path is `merkleWalkRoot`. -/
private theorem stepMerkleWalk_eq (domainTag : Goldilocks) (pkSeed : Lane4) (layer tree : Nat)
    (addr : Nat → Nat → Nat) (sib : Nat → Lane4) (W : Nat → Lane4) (idx0 h : Nat)
    (hStep : ∀ l < h, W (l + 1) =
      if (idx0 / 2 ^ l) % 2 == 0 then
        merkleAddrNodeHash domainTag pkSeed layer tree addr (1 + l) (idx0 / 2 ^ (l + 1)) (W l) (sib l)
      else
        merkleAddrNodeHash domainTag pkSeed layer tree addr (1 + l) (idx0 / 2 ^ (l + 1)) (sib l) (W l)) :
    merkleWalkRoot domainTag pkSeed layer tree addr 1 idx0 (W 0) ((List.range h).map sib) = W h := by
  have hGen : ∀ n l, l + n = h →
      merkleWalkRoot domainTag pkSeed layer tree addr (1 + l) (idx0 / 2 ^ l) (W l)
        ((List.range' l n).map sib) = W h := by
    intro n
    induction n with
    | zero =>
      intro l hl
      have e : l = h := by omega
      rw [e]
      rfl
    | succ n ih =>
      intro l hl
      have hs := hStep l (by omega)
      have hIdx : idx0 / 2 ^ l / 2 = idx0 / 2 ^ (l + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      have hI := ih (l + 1) (by omega)
      rw [hs, ← hIdx] at hI
      exact hI
  have h0 := hGen h 0 (by omega)
  rw [Nat.pow_zero, Nat.div_one, ← List.range_eq_range'] at h0
  exact h0

private theorem stepNodeHashF_xmss (pkSeed : Lane4) (layer tree l parent : Nat) (left right : Lane4)
    (hl : layer < 65536) (hlv : 1 + l < 65536) (hp : parent < 2 ^ 32) :
    stepNodeHashF domainMerkleNode (‹layer * 2 ^ 48 + (l + 1) * 2 ^ 32› +ₚ ‹parent›)
        ‹tree % 2 ^ 32› ‹(tree / 2 ^ 32) % 2 ^ 32› pkSeed left right =
      merkleAddrNodeHash domainMerkleNode pkSeed layer tree xmssNodeAddr (1 + l) parent left right := by
  unfold merkleAddrNodeHash merkleNodeHash xmssNodeAddr stepNodeHashF
  rw [← g_ofNat_add, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hlv, Nat.mod_eq_of_lt hp,
    Nat.add_comm 1 l]

/-- **Merkle rows.** The `2 * h` rows of an authentication path walk `merkleWalkRoot` from the
    node in `ST_WORK` at leaf index `idx0`; the cursor halving forces `idx0 < 2 ^ h`. The node
    address limbs are abstract: `hNode` relates the row's address limb to the addressing
    `addr` of the walked tree. -/
theorem stepMerkle_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {tag : Goldilocks} {M : Nat → Goldilocks} {layerV treeV : Nat} {addr : Nat → Nat → Nat}
    {h t1 idx0 : Nat}
    (hA : ∀ l < h, StepMerkleARow pub R (t1 + 2 * l) tag (M l))
    (hBin : ∀ l < h, (R (t1 + 2 * l + 1)).stIn = stepMerkleBIn (stepRegsAt R (t1 + 2 * l + 1)))
    (hBnext : ∀ l, l + 1 < h → stepRegsAt R (t1 + 2 * l + 2) =
      { stepRegsAt R (t1 + 2 * l + 1) with work := (stepPermAt R (t1 + 2 * l + 1)).b0 })
    (hLastCur : (stepRegsAt R (t1 + 2 * (h - 1) + 1)).cursor = Goldilocks.zero)
    (hCur : (stepRegsAt R t1).cursor = ‹idx0›)
    (hIdx : idx0 < 2 ^ 28) (hh : 0 < h) (hh28 : h ≤ 28)
    (hNode : ∀ l < h, StepFrameSWC (stepRegsAt R (t1 + 2 * l)) (stepRegsAt R t1) →
      ∀ (L Rr : Lane4),
      stepNodeHashF tag (M l +ₚ ‹idx0 / 2 ^ (l + 1)›) (stepRegsAt R t1).treeLo
          (stepRegsAt R t1).treeHi pub.1.pkSeed L Rr =
        merkleAddrNodeHash tag pub.1.pkSeed layerV treeV addr (1 + l) (idx0 / 2 ^ (l + 1)) L Rr) :
    idx0 < 2 ^ h ∧
    merkleWalkRoot tag pub.1.pkSeed layerV treeV addr 1 idx0
        (stepRegsAt R t1).work ((List.range h).map (fun l => stepAuxLane R (t1 + 2 * l) 2)) =
      (stepPermAt R (t1 + 2 * (h - 1) + 1)).b0 ∧
    StepFrameSWC (stepRegsAt R (t1 + 2 * (h - 1) + 1)) (stepRegsAt R t1) := by
  let X : Nat → Goldilocks := fun l => match l with
    | 0 => ‹idx0›
    | l + 1 => stepAux R (t1 + 2 * l) 1
  let W : Nat → Lane4 := fun l => match l with
    | 0 => (stepRegsAt R t1).work
    | l + 1 => (stepPermAt R (t1 + 2 * l + 1)).b0
  have hA1 : ∀ l, l < h →
      (stepRegsAt R (t1 + 2 * l + 1)).cursor = stepAux R (t1 + 2 * l) 1 ∧
      StepFrameSWC (stepRegsAt R (t1 + 2 * l + 1)) (stepRegsAt R (t1 + 2 * l)) := by
    intro l hl'
    rw [(hA l hl').next]
    exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hInv : ∀ l, l < h →
      (stepRegsAt R (t1 + 2 * l)).cursor = X l ∧
      (stepRegsAt R (t1 + 2 * l)).work = W l ∧
      StepFrameSWC (stepRegsAt R (t1 + 2 * l)) (stepRegsAt R t1) := by
    intro l
    induction l with
    | zero => intro _; exact ⟨hCur, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    | succ l ih =>
      intro hl'
      obtain ⟨_, _, iF⟩ := ih (by omega)
      obtain ⟨c1, f1⟩ := hA1 l (by omega)
      have hN := hBnext l hl'
      have e : t1 + 2 * (l + 1) = t1 + 2 * l + 2 := by omega
      rw [e, hN]
      exact ⟨c1, rfl, ⟨f1.curRoot.trans iF.curRoot, f1.kp.trans iF.kp,
        f1.treeLo.trans iF.treeLo, f1.treeHi.trans iF.treeHi, f1.rem.trans iF.rem,
        f1.main.trans iF.main⟩⟩
  have hStepX : ∀ l < h, (stepAux R (t1 + 2 * l) 0).val < 2 ∧
      X l = ‹(stepAux R (t1 + 2 * l) 0).val› +ₚ (X (l + 1) *ₚ ‹2›) := by
    intro l hl'
    have hb := (hA l hl').bit
    have hc := (hA l hl').cur
    obtain ⟨iC, _, _⟩ := hInv l hl'
    refine ⟨by rcases hb with hb | hb <;> rw [hb] <;> decide, ?_⟩
    rw [← iC, hc, g_ofNat_self]
    show _ = stepAux R (t1 + 2 * l) 0 +ₚ (stepAux R (t1 + 2 * l) 1 *ₚ ‹2›)
    have h2 : (‹2› : Goldilocks) = Goldilocks.one +ₚ Goldilocks.one := by decide +kernel
    rw [h2, g_left_distrib, g_mul_one, g_add_assoc]
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have hEndX : X (h' + 1) = Goldilocks.zero := by
    obtain ⟨c1, _⟩ := hA1 h' (by omega)
    show stepAux R (t1 + 2 * h') 1 = Goldilocks.zero
    rw [← c1]
    exact hLastCur
  have hPow : 2 ^ (h' + 1) < goldilocksPrime :=
    Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hh28) (by decide)
  have hip : idx0 < goldilocksPrime := Nat.lt_trans hIdx (by decide)
  have hX0 : (X 0).val = idx0 := Nat.mod_eq_of_lt hip
  obtain ⟨hLt, hBits⟩ := stepHalving_chain X (fun l => (stepAux R (t1 + 2 * l) 0).val) (h' + 1)
    hStepX hEndX hPow
  rw [hX0] at hLt hBits
  have hXval : ∀ l, l ≤ h' + 1 → X l = ‹idx0 / 2 ^ l› := by
    intro l hl'
    rw [← (hBits l hl').1, g_ofNat_self]
  have hStepW : ∀ l < h' + 1, W (l + 1) =
      if (idx0 / 2 ^ l) % 2 == 0 then
        merkleAddrNodeHash tag pub.1.pkSeed layerV treeV addr (1 + l)
          (idx0 / 2 ^ (l + 1)) (W l) (stepAuxLane R (t1 + 2 * l) 2)
      else
        merkleAddrNodeHash tag pub.1.pkSeed layerV treeV addr (1 + l)
          (idx0 / 2 ^ (l + 1)) (stepAuxLane R (t1 + 2 * l) 2) (W l) := by
    intro l hl'
    have hb := (hA l hl').bit
    have hH := stepMerkleLevel_hash (hA l hl') (hBin l hl')
    obtain ⟨_, iW, iF⟩ := hInv l hl'
    have hY : stepAux R (t1 + 2 * l) 1 = ‹idx0 / 2 ^ (l + 1)› := hXval (l + 1) (by omega)
    have hBit := (hBits l (by omega)).2 hl'
    show (stepPermAt R (t1 + 2 * l + 1)).b0 = _
    rw [hH, hY, iF.treeLo, iF.treeHi, iW, hNode l hl' iF]
    rcases hb with hb | hb
    · have h0 : (idx0 / 2 ^ l) % 2 = 0 := by rw [← hBit, hb]; rfl
      rw [hb, lane4MuxL_zero, lane4Mux_zero, h0]
      rfl
    · have h1 : (idx0 / 2 ^ l) % 2 = 1 := by rw [← hBit, hb]; rfl
      rw [hb, lane4MuxL_one, lane4Mux_one, h1]
      rfl
  have hWalk := stepMerkleWalk_eq tag pub.1.pkSeed layerV treeV addr
    (fun l => stepAuxLane R (t1 + 2 * l) 2) W idx0 (h' + 1) hStepW
  obtain ⟨_, _, iF⟩ := hInv h' (by omega)
  obtain ⟨_, f1⟩ := hA1 h' (by omega)
  have e : h' + 1 - 1 = h' := by omega
  rw [e]
  exact ⟨hLt, hWalk, ⟨f1.curRoot.trans iF.curRoot, f1.kp.trans iF.kp,
    f1.treeLo.trans iF.treeLo, f1.treeHi.trans iF.treeHi, f1.rem.trans iF.rem,
    f1.main.trans iF.main⟩⟩

/-! ### §3.11. `HmsgDecompLimb` rows: the packed remaining-step counts and the target sum -/

/-- Limb `l` of a `Digest5` (the last limb for `l ≥ 4`). -/
def digest5Limb (d : Digest5) : Nat → Goldilocks
  | 0 => d.limb0
  | 1 => d.limb1
  | 2 => d.limb2
  | 3 => d.limb3
  | _ => d.limb4

/-- Base-4 digit of chain `c`: digit `c % 31` of limb `c / 31`. -/
def stepDigit (d : Digest5) (c : Nat) : Nat :=
  ((digest5Limb d (c / 31)).val / 4 ^ (c % 31)) % 4

/-- The `H_msg` digest held in the first five limbs of `ST_MAIN_SPONGE`. -/
def stepHmsgOf (m : Poseidon2State12) : Digest5 :=
  ⟨m.b0.x0, m.b0.x1, m.b0.x2, m.b0.x3, m.b1.x0⟩

/-- Digits `dig c` of the items `cs` owned by slot `s`, packed in base `B` from the first item
    `start s` of the slot, accumulated onto `a`. -/
def stepPackFoldG (B : Nat) (slotOf start : Nat → Nat) (dig : Nat → Nat) (s : Nat)
    (cs : List Nat) (a : Nat) : Nat :=
  cs.foldl (fun acc c => if slotOf c = s then acc + dig c * B ^ (c - start s) else acc) a

/-- Remaining-step counts `3 - dg c` of the chains `cs` owned by slot `s`, packed two bits per
    chain from the first chain of the slot, accumulated onto `a`. -/
def stepPackFold (dg : Nat → Nat) (s : Nat) (cs : List Nat) (a : Nat) : Nat :=
  stepPackFoldG 4 wotsPackSlot wotsPackSlotStart (fun c => 3 - dg c) s cs a

private theorem g_ofNat_sub_of_le {a b : Nat} (h : b ≤ a) : (‹a› : Goldilocks) -ₚ ‹b› = ‹a - b› := by
  have h1 : (‹b› : Goldilocks) +ₚ (‹a› -ₚ ‹b›) = ‹a› := LawfulCommRing.add_sub_cancel_left _ _
  have h2 : (‹b› : Goldilocks) +ₚ ‹a - b› = ‹a› := by
    rw [← g_ofNat_add]
    exact congrArg Goldilocks.ofNat (by omega)
  exact LawfulCommRing.add_left_cancel (h1.trans h2.symm)

private theorem range'_split : ∀ (m s n : Nat),
    List.range' s (m + n) = List.range' s m ++ List.range' (s + m) n
  | 0, s, n => by simp
  | m + 1, s, n => by
    have e : m + 1 + n = (m + n) + 1 := by omega
    have e2 : s + (m + 1) = s + 1 + m := by omega
    rw [e, e2]
    show s :: List.range' (s + 1) (m + n) = s :: (List.range' (s + 1) m ++ _)
    rw [range'_split m (s + 1) n]

private theorem mem_range'_bounds : ∀ (n s c : Nat), c ∈ List.range' s n → s ≤ c ∧ c < s + n
  | 0, _, _, h => absurd h List.not_mem_nil
  | n + 1, s, c, h => by
    have e : List.range' s (n + 1) = s :: List.range' (s + 1) n := rfl
    rw [e, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨Nat.le_refl _, by omega⟩
    · have h' := mem_range'_bounds n (s + 1) c h
      exact ⟨by omega, by omega⟩

private theorem range'_eq_map (s n : Nat) :
    List.range' s n = (List.range n).map (fun i => s + i) :=
  List.range'_eq_map_range

private theorem stepPackFold_field (x : StepOpRowInputs) (dg : Nat → Nat) (l s : Nat) :
    ∀ (is : List Nat) (A : Nat),
      (∀ i ∈ is, x.aux i = ‹dg (31 * l + i)› ∧ dg (31 * l + i) ≤ 3) →
      is.foldl (fun acc i =>
          if stRemPack + wotsPackSlot (31 * l + i) = stRemPack + s then
            acc +ₚ ((‹3› -ₚ x.aux i) *ₚ
              ‹2 ^ (2 * (31 * l + i - wotsPackSlotStart (wotsPackSlot (31 * l + i))))›)
          else acc) ‹A› =
        ‹stepPackFold dg s (is.map (fun i => 31 * l + i)) A›
  | [], _, _ => rfl
  | i :: rest, A, h => by
    obtain ⟨hAux, hLe⟩ := h i (List.mem_cons_self ..)
    have ih := fun A' => stepPackFold_field x dg l s rest A'
      (fun j hj => h j (List.mem_cons_of_mem _ hj))
    rw [List.foldl_cons, List.map_cons]
    unfold stepPackFold stepPackFoldG
    rw [List.foldl_cons]
    by_cases hc : wotsPackSlot (31 * l + i) = s
    · simp only [hc, ↓reduceIte]
      have hStep : (‹A› : Goldilocks) +ₚ ((‹3› -ₚ x.aux i) *ₚ
          ‹2 ^ (2 * (31 * l + i - wotsPackSlotStart s))›) =
          ‹A + (3 - dg (31 * l + i)) * 4 ^ (31 * l + i - wotsPackSlotStart s)› := by
        rw [hAux, g_ofNat_sub_of_le hLe, ← g_ofNat_mul, ← g_ofNat_add, Nat.pow_mul]
      rw [hStep]
      exact ih _
    · have hcond : ¬ (stRemPack + wotsPackSlot (31 * l + i) = stRemPack + s) :=
        fun h' => hc (Nat.add_left_cancel h')
      simp only [hcond, hc, ↓reduceIte]
      exact ih _

private theorem stepPlainSum_field (x : StepOpRowInputs) (dg : Nat → Nat) (l : Nat) :
    ∀ (is : List Nat) (A : Nat),
      (∀ i ∈ is, x.aux i = ‹dg (31 * l + i)›) →
      is.foldl (fun acc i => acc +ₚ x.aux i) ‹A› =
        ‹A + listNatSum (is.map (fun i => dg (31 * l + i)))›
  | [], _, _ => rfl
  | i :: rest, A, h => by
    rw [List.foldl_cons, h i (List.mem_cons_self ..), ← g_ofNat_add,
      stepPlainSum_field x dg l rest _ (fun j hj => h j (List.mem_cons_of_mem _ hj)),
      List.map_cons]
    exact congrArg Goldilocks.ofNat (by simp only [listNatSum]; omega)

private theorem listNatSum_append : ∀ (a b : List Nat),
    listNatSum (a ++ b) = listNatSum a + listNatSum b
  | [], _ => by simp [listNatSum]
  | x :: a, b => by
    rw [List.cons_append]
    simp only [listNatSum]
    rw [listNatSum_append a b]
    omega

private theorem listNatSum_le (k : Nat) : ∀ (l : List Nat), (∀ x ∈ l, x ≤ k) →
    listNatSum l ≤ k * l.length
  | [], _ => by simp [listNatSum]
  | x :: l, h => by
    have hx := h x (List.mem_cons_self ..)
    have ih := listNatSum_le k l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [listNatSum, List.length_cons, Nat.mul_succ]
    omega

private theorem stepDigit_le (d : Digest5) (c : Nat) : stepDigit d c ≤ 3 := by
  unfold stepDigit
  have := Nat.mod_lt ((digest5Limb d (c / 31)).val / 4 ^ (c % 31)) (by decide : 0 < 4)
  omega

/-- Number of digits read from limb `l`. -/
def stepLimbDigits (l : Nat) : Nat := if l < 4 then 31 else 4

/-- **`HmsgDecompLimb l` row.** The limb is `< 2^63`; its digits' remaining-step counts are
    added to the `ST_REM_PACK` limbs and the digits to the accumulator; nothing else changes. -/
theorem stepDecomp_row {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow} {l t : Nat}
    (hl : l < 5) (h : StepRowSem pub R (.hmsgDecompLimb l) t) (A : Nat → Nat) (B : Nat)
    (hRem : ∀ s < 6, (stepRegsAt R t).rem.get s = ‹A s›)
    (hAcc : (stepRegsAt R t).acc = ‹B›) :
    (digest5Limb (stepHmsgOf (stepRegsAt R t).main) l).val < 2 ^ 63 ∧
    (∀ s < 6, (stepRegsAt R (t + 1)).rem.get s =
      ‹stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s
        (List.range' (31 * l) (stepLimbDigits l)) (A s)›) ∧
    (stepRegsAt R (t + 1)).acc =
      ‹B + listNatSum ((List.range' (31 * l) (stepLimbDigits l)).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main)))› ∧
    (l = 4 → (‹B + listNatSum ((List.range' (31 * l) (stepLimbDigits l)).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main)))› : Goldilocks) = ‹192›) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := (stepRegsAt R (t + 1)).rem, acc := (stepRegsAt R (t + 1)).acc } := by
  obtain ⟨hD, h192, hR⟩ := stepSem_hmsgDecompLimb hl h
  obtain ⟨hLt, hAux, _⟩ := (stepLimb63Decomp_allZero_iff _ l).mp hD
  have hLimb : (stepOpRowInputsPerm pub (R t)).prev (stMainSponge + l) =
      digest5Limb (stepHmsgOf (stepRegsAt R t).main) l := by
    rcases l with _ | _ | _ | _ | _ | l
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hl (by omega)
  rw [hLimb] at hLt hAux
  have hn : stepLimbDigits l ≤ 31 := by unfold stepLimbDigits; split <;> omega
  have hDig : ∀ i < stepLimbDigits l,
      (stepOpRowInputsPerm pub (R t)).aux i =
        ‹stepDigit (stepHmsgOf (stepRegsAt R t).main) (31 * l + i)› := by
    intro i hi
    have e1 : (31 * l + i) / 31 = l := by omega
    have e2 : (31 * l + i) % 31 = i := by omega
    unfold stepDigit
    rw [e1, e2]
    exact hAux i (by omega)
  have hRemE : ∀ s < 6, stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l (stRemPack + s) =
      ‹stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s
        (List.range' (31 * l) (stepLimbDigits l)) (A s)› := by
    intro s hs
    have hPrev : (stepOpRowInputsPerm pub (R t)).prev (stRemPack + s) = ‹A s› := by
      rw [← hRem s hs]
      rcases s with _ | _ | _ | _ | _ | _ | s
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd hs (by omega)
    have hne : ¬ (stRemPack + s = stAccOrU1) := by unfold stRemPack stAccOrU1; omega
    unfold stepHmsgDecompExpected
    simp only [hne, ↓reduceIte]
    rw [hPrev, range'_eq_map]
    exact stepPackFold_field _ _ l s _ (A s)
      (fun i hi => ⟨hDig i (List.mem_range.mp hi), stepDigit_le _ _⟩)
  have hAccE : stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l stAccOrU1 =
      ‹B + listNatSum ((List.range' (31 * l) (stepLimbDigits l)).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main)))› := by
    have hPrev : (stepOpRowInputsPerm pub (R t)).prev stAccOrU1 = ‹B› := hAcc
    have hS := stepPlainSum_field (stepOpRowInputsPerm pub (R t))
      (stepDigit (stepHmsgOf (stepRegsAt R t).main)) l (List.range (stepLimbDigits l)) 0
      (fun i hi => hDig i (List.mem_range.mp hi))
    unfold stepHmsgDecompExpected
    simp only [↓reduceIte]
    rw [hPrev]
    show ‹B› +ₚ (List.range (stepLimbDigits l)).foldl
      (fun acc i => acc +ₚ (stepOpRowInputsPerm pub (R t)).aux i) ‹0› = _
    rw [hS, ← g_ofNat_add, range'_eq_map, List.map_map, Nat.zero_add]
    rfl
  have hRemGet : ∀ s < 6, (stepRegsAt R (t + 1)).rem.get s =
      stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l (stRemPack + s) := by
    intro s hs
    rw [hR]
    rcases s with _ | _ | _ | _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hs (by omega)
  have hAccGet : (stepRegsAt R (t + 1)).acc =
      stepHmsgDecompExpected (stepOpRowInputsPerm pub (R t)) l stAccOrU1 := by rw [hR]
  refine ⟨hLt, fun s hs => (hRemGet s hs).trans (hRemE s hs), hAccGet.trans hAccE,
    fun h4 => hAccE.symm.trans (h192 h4), ?_⟩
  rw [hR]

private theorem stepPackFoldG_append (B : Nat) (slotOf start dig : Nat → Nat) (s : Nat)
    (xs ys : List Nat) (a : Nat) :
    stepPackFoldG B slotOf start dig s (xs ++ ys) a =
      stepPackFoldG B slotOf start dig s ys (stepPackFoldG B slotOf start dig s xs a) := by
  unfold stepPackFoldG
  rw [List.foldl_append]

private theorem stepPackFoldG_skip (B : Nat) (slotOf start dig : Nat → Nat) (s : Nat) :
    ∀ (cs : List Nat) (a : Nat), (∀ c ∈ cs, slotOf c ≠ s) →
      stepPackFoldG B slotOf start dig s cs a = a
  | [], _, _ => rfl
  | c :: cs, a, h => by
    have hc := h c (List.mem_cons_self ..)
    unfold stepPackFoldG
    rw [List.foldl_cons]
    simp only [hc, ↓reduceIte]
    exact stepPackFoldG_skip B slotOf start dig s cs a
      (fun y hy => h y (List.mem_cons_of_mem _ hy))

private theorem stepPackFoldG_run (B : Nat) (slotOf start dig : Nat → Nat) (s : Nat) :
    ∀ (len b acc : Nat), start s ≤ b →
      (∀ c ∈ List.range' b len, slotOf c = s) →
      stepPackFoldG B slotOf start dig s (List.range' b len) acc =
        acc + B ^ (b - start s) * evalBaseDigits B ((List.range' b len).map dig)
  | 0, b, acc, _, _ => by
    show acc = acc + B ^ (b - start s) * 0
    rw [Nat.mul_zero, Nat.add_zero]
  | len + 1, b, acc, hab, h => by
    have e : List.range' b (len + 1) = b :: List.range' (b + 1) len := rfl
    have hb : slotOf b = s := h b (by rw [e]; exact List.mem_cons_self ..)
    have ih := stepPackFoldG_run B slotOf start dig s len (b + 1)
      (acc + dig b * B ^ (b - start s))
      (by omega) (fun c hc => h c (by rw [e]; exact List.mem_cons_of_mem _ hc))
    have hStep : stepPackFoldG B slotOf start dig s (List.range' b (len + 1)) acc =
        stepPackFoldG B slotOf start dig s (List.range' (b + 1) len)
          (acc + dig b * B ^ (b - start s)) := by
      rw [e]
      unfold stepPackFoldG
      rw [List.foldl_cons]
      simp only [hb, ↓reduceIte]
    have hP : B ^ (b + 1 - start s) = B ^ (b - start s) * B := by
      rw [show b + 1 - start s = (b - start s) + 1 by omega, Nat.pow_succ]
    rw [hStep, ih, e, List.map_cons]
    show acc + dig b * B ^ (b - start s) +
        B ^ (b + 1 - start s) * evalBaseDigits B ((List.range' (b + 1) len).map dig) =
      acc + B ^ (b - start s) *
        (dig b + B * evalBaseDigits B ((List.range' (b + 1) len).map dig))
    rw [hP, Nat.mul_add, Nat.mul_comm (dig b), Nat.mul_assoc, Nat.add_assoc]

/-- The packed limb of slot `s` over all `N` items is the base-`B` number of the digits of the
    items `[a, a + len)` the slot owns. -/
private theorem stepPackFoldG_slot (B : Nat) (slotOf start dig : Nat → Nat) (N s a len : Nat)
    (hRange : ∀ c < N, slotOf c = s ↔ a ≤ c ∧ c < a + len) (haN : a + len ≤ N)
    (hStart : start s = a) :
    stepPackFoldG B slotOf start dig s (List.range' 0 N) 0 =
      evalBaseDigits B ((List.range' a len).map dig) := by
  have e : List.range' 0 N =
      List.range' 0 a ++ (List.range' a len ++ List.range' (a + len) (N - (a + len))) := by
    have h1 := range'_split a 0 (N - a)
    have h2 := range'_split len a (N - (a + len))
    rw [show a + (N - a) = N by omega, Nat.zero_add] at h1
    rw [show len + (N - (a + len)) = N - a by omega] at h2
    rw [h1, h2]
  have s1 := stepPackFoldG_skip B slotOf start dig s (List.range' 0 a) 0 (fun c hc h' => by
    have hb := mem_range'_bounds _ _ _ hc
    have := (hRange c (by omega)).mp h'
    omega)
  have s2 := stepPackFoldG_run B slotOf start dig s len a 0 (by omega) (fun c hc => by
    have hb := mem_range'_bounds _ _ _ hc
    exact (hRange c (by omega)).mpr hb)
  have s3 := fun acc => stepPackFoldG_skip B slotOf start dig s
    (List.range' (a + len) (N - (a + len))) acc
    (fun c hc h' => by
      have hb := mem_range'_bounds _ _ _ hc
      have := (hRange c (by omega)).mp h'
      omega)
  rw [e, stepPackFoldG_append, stepPackFoldG_append, s1, s2, s3, hStart, Nat.sub_self,
    Nat.pow_zero, Nat.one_mul, Nat.zero_add]

private theorem stepPackFold_append (dg : Nat → Nat) (s : Nat) (xs ys : List Nat) (a : Nat) :
    stepPackFold dg s (xs ++ ys) a = stepPackFold dg s ys (stepPackFold dg s xs a) :=
  stepPackFoldG_append _ _ _ _ _ _ _ _

/-- The packed limb of slot `s` over all 128 chains is the base-4 number of the
    remaining-step counts of the chains `[a, a + len)` the slot owns. -/
private theorem stepPackFold_slot (dg : Nat → Nat) (s a len : Nat)
    (hRange : ∀ c < 128, wotsPackSlot c = s ↔ a ≤ c ∧ c < a + len) (haN : a + len ≤ 128)
    (hStart : wotsPackSlotStart s = a) :
    stepPackFold dg s (List.range' 0 128) 0 =
      evalBaseDigits 4 ((List.range' a len).map (fun c => 3 - dg c)) :=
  stepPackFoldG_slot 4 wotsPackSlot wotsPackSlotStart (fun c => 3 - dg c) 128 s a len hRange haN
    hStart

private theorem range'_128_split :
    List.range' 0 128 =
      List.range' 0 31 ++ List.range' 31 31 ++ List.range' 62 31 ++ List.range' 93 31 ++
        List.range' 124 4 := by
  decide

private theorem goldilocksPrime_eq : goldilocksPrime = 18446744069414584321 := rfl

/-- **`HmsgDecompLimb` rows.** The five rows check every limb `< 2^63`, leave in each
    `ST_REM_PACK` limb the packed remaining-step counts of its chains, and enforce the target
    sum `192` of the 128 digits. -/
theorem stepDecomp_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow} {t : Nat}
    (hRun : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) t)
    (hRem0 : ∀ s < 6, (stepRegsAt R t).rem.get s = Goldilocks.zero)
    (hAcc0 : (stepRegsAt R t).acc = Goldilocks.zero) :
    checkDigest5Limbs63 (stepHmsgOf (stepRegsAt R t).main) = true ∧
    (∀ s < 6, (stepRegsAt R (t + 5)).rem.get s =
      ‹stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 0 128) 0›) ∧
    listNatSum ((List.range' 0 128).map (stepDigit (stepHmsgOf (stepRegsAt R t).main))) = 192 ∧
    (stepRegsAt R (t + 5)).main = (stepRegsAt R t).main ∧
    (stepRegsAt R (t + 5)).curRoot = (stepRegsAt R t).curRoot ∧
    (stepRegsAt R (t + 5)).kp = (stepRegsAt R t).kp ∧
    (stepRegsAt R (t + 5)).treeLo = (stepRegsAt R t).treeLo ∧
    (stepRegsAt R (t + 5)).treeHi = (stepRegsAt R t).treeHi := by
  have hz : (‹0› : Goldilocks) = Goldilocks.zero := Goldilocks.ext rfl
  have h0 : StepRowSem pub R (.hmsgDecompLimb 0) t := hRun.map_range 0 (by decide)
  have h1 : StepRowSem pub R (.hmsgDecompLimb 1) (t + 1) := hRun.map_range 1 (by decide)
  have h2 : StepRowSem pub R (.hmsgDecompLimb 2) (t + 2) := hRun.map_range 2 (by decide)
  have h3 : StepRowSem pub R (.hmsgDecompLimb 3) (t + 3) := hRun.map_range 3 (by decide)
  have h4 : StepRowSem pub R (.hmsgDecompLimb 4) (t + 4) := hRun.map_range 4 (by decide)
  obtain ⟨l0, r0, a0, _, f0⟩ := stepDecomp_row (by decide) h0 (fun _ => 0) 0
    (fun s hs => (hRem0 s hs).trans hz.symm) (hAcc0.trans hz.symm)
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r0 a0
  have m1 : (stepRegsAt R (t + 1)).main = (stepRegsAt R t).main := by rw [f0]
  obtain ⟨l1, r1, a1, _, f1⟩ := stepDecomp_row (by decide) h1 _ _ r0 a0
  have f1' : stepRegsAt R (t + 2) = _ := f1
  rw [m1] at l1 r1 a1
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r1 a1
  have m2 : (stepRegsAt R (t + 2)).main = (stepRegsAt R t).main := by rw [f1']; exact m1
  obtain ⟨l2, r2, a2, _, f2⟩ := stepDecomp_row (by decide) h2 _ _ r1 a1
  have f2' : stepRegsAt R (t + 3) = _ := f2
  rw [m2] at l2 r2 a2
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r2 a2
  have m3 : (stepRegsAt R (t + 3)).main = (stepRegsAt R t).main := by rw [f2']; exact m2
  obtain ⟨l3, r3, a3, _, f3⟩ := stepDecomp_row (by decide) h3 _ _ r2 a2
  have f3' : stepRegsAt R (t + 4) = _ := f3
  rw [m3] at l3 r3 a3
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r3 a3
  have m4 : (stepRegsAt R (t + 4)).main = (stepRegsAt R t).main := by rw [f3']; exact m3
  obtain ⟨l4, r4, _, e192, f4⟩ := stepDecomp_row (by decide) h4 _ _ r3 a3
  have f4' : stepRegsAt R (t + 5) = _ := f4
  have e192' := e192 rfl
  rw [m4] at l4 r4 e192'
  simp only [stepLimbDigits, Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r4 e192'
  have m5 : (stepRegsAt R (t + 5)).main = (stepRegsAt R t).main := by rw [f4']; exact m4
  refine ⟨?_, ?_, ?_, m5, ?_, ?_, ?_, ?_⟩
  · unfold checkDigest5Limbs63
    have q0 : (stepHmsgOf (stepRegsAt R t).main).limb0.val < 2 ^ 63 := l0
    have q1 : (stepHmsgOf (stepRegsAt R t).main).limb1.val < 2 ^ 63 := l1
    have q2 : (stepHmsgOf (stepRegsAt R t).main).limb2.val < 2 ^ 63 := l2
    have q3 : (stepHmsgOf (stepRegsAt R t).main).limb3.val < 2 ^ 63 := l3
    have q4 : (stepHmsgOf (stepRegsAt R t).main).limb4.val < 2 ^ 63 := l4
    simp only [q0, q1, q2, q3, q4, decide_true, Bool.and_self]
  · intro s hs
    have h := r4 s hs
    have e : stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 0 128) 0 =
        stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 124 4)
          (stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 93 31)
            (stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 62 31)
              (stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s (List.range' 31 31)
                (stepPackFold (stepDigit (stepHmsgOf (stepRegsAt R t).main)) s
                  (List.range' 0 31) 0)))) := by
      rw [range'_128_split, stepPackFold_append, stepPackFold_append, stepPackFold_append,
        stepPackFold_append]
    rw [e]
    exact h
  · have hv := congrArg Goldilocks.val e192'
    simp only [Goldilocks.ofNat_val] at hv
    have hLe : ∀ (b n : Nat), listNatSum ((List.range' b n).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main))) ≤ 3 * n := by
      intro b n
      have h := listNatSum_le 3 ((List.range' b n).map
        (stepDigit (stepHmsgOf (stepRegsAt R t).main))) (fun x hx => by
          obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
          exact stepDigit_le _ _)
      rw [List.length_map, List.length_range'] at h
      exact h
    have b0 := hLe 0 31
    have b1 := hLe 31 31
    have b2 := hLe 62 31
    have b3 := hLe 93 31
    have b4 := hLe 124 4
    rw [goldilocksPrime_eq] at hv
    rw [range'_128_split, List.map_append, List.map_append, List.map_append, List.map_append,
      listNatSum_append, listNatSum_append, listNatSum_append, listNatSum_append]
    omega
  · rw [f4', f3', f2', f1', f0]
  · rw [f4', f3', f2', f1', f0]
  · rw [f4', f3', f2', f1', f0]
  · rw [f4', f3', f2', f1', f0]

private theorem extractLimbBase4Digits_eq_map (n v : Nat) :
    extractLimbBase4Digits n v = (List.range n).map (fun i => (v / 4 ^ i) % 4) := by
  apply List.ext_getElem
  · rw [extractLimbBase4Digits_length, List.length_map, List.length_range]
  · intro i h1 h2
    rw [extractLimbBase4Digits_getElem n v i h1, List.getElem_map, List.getElem_range]

private theorem stepDigit_segment (d : Digest5) (l n : Nat) (hn : n ≤ 31) :
    (List.range' (31 * l) n).map (stepDigit d) =
      extractLimbBase4Digits n (digest5Limb d l).val := by
  rw [extractLimbBase4Digits_eq_map, range'_eq_map, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have e1 : (31 * l + i) / 31 = l := by omega
  have e2 : (31 * l + i) % 31 = i := by omega
  show stepDigit d (31 * l + i) = _
  unfold stepDigit
  rw [e1, e2]

/-- The 128 digits `stepDigit` are the digits the native verifier extracts. -/
theorem stepDigits_extract (geom : AggSigGeometry) (d : Digest5)
    (hw : geom.wotsChains = 128) (hChk : checkDigest5Limbs63 d = true) :
    extractWotsDigitsChecked geom d = some ((List.range' 0 128).map (stepDigit d)) := by
  have s0 : (List.range' 0 31).map (stepDigit d) = extractLimbBase4Digits 31 d.limb0.val :=
    stepDigit_segment d 0 31 (by decide)
  have s1 : (List.range' 31 31).map (stepDigit d) = extractLimbBase4Digits 31 d.limb1.val :=
    stepDigit_segment d 1 31 (by decide)
  have s2 : (List.range' 62 31).map (stepDigit d) = extractLimbBase4Digits 31 d.limb2.val :=
    stepDigit_segment d 2 31 (by decide)
  have s3 : (List.range' 93 31).map (stepDigit d) = extractLimbBase4Digits 31 d.limb3.val :=
    stepDigit_segment d 3 31 (by decide)
  have s4 : (List.range' 124 4).map (stepDigit d) = extractLimbBase4Digits 4 d.limb4.val :=
    stepDigit_segment d 4 4 (by decide)
  unfold extractWotsDigitsChecked
  rw [hChk, range'_128_split, List.map_append, List.map_append, List.map_append,
    List.map_append, s0, s1, s2, s3, s4, hw]
  simp only [↓reduceIte]
  rw [List.take_of_length_le (by simp [extractLimbBase4Digits_length])]

/-! ### §3.12. One full layer: digits, WOTS+C and Merkle rows give `verifyWotsLayer` -/

private theorem mem_range'_of_bounds : ∀ (n s c : Nat), s ≤ c → c < s + n → c ∈ List.range' s n
  | 0, _, _, _, _ => by omega
  | n + 1, s, c, h1, h2 => by
    have e : List.range' s (n + 1) = s :: List.range' (s + 1) n := rfl
    rw [e, List.mem_cons]
    by_cases hc : c = s
    · exact .inl hc
    · exact .inr (mem_range'_of_bounds n (s + 1) c (by omega) (by omega))

private theorem recoverAggWotsEndpoints_map (pkSeed : Lane4) (layer tree kpN : Nat)
    (dg : Nat → Nat) (a : Nat → Lane4) :
    ∀ (n c0 : Nat),
      recoverAggWotsEndpoints pkSeed layer tree kpN c0 ((List.range' c0 n).map dg)
          ((List.range' c0 n).map a) =
        (List.range' c0 n).map
          (fun c => wotsChainWalk pkSeed layer tree kpN c (dg c) (3 - dg c) (a c))
  | 0, _ => rfl
  | n + 1, c0 => by
    have e : List.range' c0 (n + 1) = c0 :: List.range' (c0 + 1) n := rfl
    rw [e, List.map_cons, List.map_cons, List.map_cons,
      ← recoverAggWotsEndpoints_map pkSeed layer tree kpN dg a n (c0 + 1)]
    rfl

theorem stepWotsOps_length (layer : Nat) : (stepWotsOps layer).length = 450 := by
  unfold stepWotsOps
  rw [List.length_append, List.length_append, flatMap_range_uniform_length _ 7 (fun _ => rfl)]
  rfl

/-- The 128 signature chain values read from the `WotsChainStep0` rows of a layer. -/
def stepLayerChains (R : Nat → StepOpRow) (t0 : Nat) : List Lane4 :=
  (List.range 128).map fun c => stepAuxLane R (stepChainRow t0 c) 0

/-- The authentication path read from the `XmssMerkleBlockA` rows starting at row `t1`. -/
def stepLayerPath (R : Nat → StepOpRow) (t1 h : Nat) : List Lane4 :=
  (List.range h).map fun l => stepAuxLane R (t1 + 2 * l) 2

/-- **Layer rows.** Five `HmsgDecompLimb` rows followed by `pushLayerWotsAndMerkle` verify one
    WOTS+C layer: with the digest in `ST_MAIN_SPONGE`, the native `verifyWotsLayer` accepts the
    chain values and authentication path read from the auxiliary columns, and returns the
    permutation output of the last `XmssMerkleBlockB` row. -/
theorem stepLayer_verify {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {geom : AggSigGeometry} {layer h tD kpN tree ctr : Nat} {isTop : Bool}
    (hDec : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) tD)
    (hLayer : StepRunAt pub R (pushLayerWotsAndMerkle layer h isTop) (tD + 5))
    (hRem0 : ∀ s < 6, (stepRegsAt R tD).rem.get s = Goldilocks.zero)
    (hAcc0 : (stepRegsAt R tD).acc = Goldilocks.zero)
    (hAddr : StepAddrOk (stepRegsAt R tD) kpN tree)
    (hLastIn : (R (tD + 455 + 2 * (h - 1) + 1)).stIn =
      stepMerkleBIn (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)))
    (hLastCur : (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)).cursor = Goldilocks.zero)
    (hl : layer < 64) (hk : kpN < 2 ^ 28) (hh : 0 < h) (hh28 : h ≤ 28)
    (hw : geom.wotsChains = 128) (hts : geom.targetSum = 192) (hsh : geom.subtreeHeight = h) :
    kpN < 2 ^ h ∧
    verifyWotsLayer geom pub.1 layer tree kpN (stepHmsgOf (stepRegsAt R tD).main)
        ⟨ctr, stepLayerChains R (tD + 5), stepLayerPath R (tD + 455) h⟩ =
      some (stepPermAt R (tD + 455 + 2 * (h - 1) + 1)).b0 ∧
    (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)).curRoot = (stepRegsAt R tD).curRoot ∧
    StepAddrOk (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)) kpN tree := by
  obtain ⟨hChk, hPack, hSum, _, hCR, hKp, hLo, hHi⟩ := stepDecomp_sem hDec hRem0 hAcc0
  obtain ⟨hm, hhm⟩ : ∃ hm, hm = stepHmsgOf (stepRegsAt R tD).main := ⟨_, rfl⟩
  rw [← hhm] at hChk hPack hSum ⊢
  have hAddr5 : StepAddrOk (stepRegsAt R (tD + 5)) kpN tree :=
    ⟨hKp.trans hAddr.kp, hLo.trans hAddr.lo, hHi.trans hAddr.hi⟩
  rw [pushLayerWotsAndMerkle_eq] at hLayer
  have e450 : tD + 5 + 450 = tD + 455 := by omega
  have hM : StepRunAt pub R (stepMerkleOps layer h isTop) (tD + 455) := by
    have h' := hLayer.append_right
    rw [stepWotsOps_length, e450] at h'
    exact h'
  obtain ⟨hd, hSlots, hWork, hCur450R, hAddr450, hCursor⟩ :=
    stepWots_sem hLayer.append_left hAddr5 hl hk
  rw [e450] at hWork hCur450R hAddr450 hCursor
  have hDigEq : ∀ s a len : Nat, (∀ c < 128, wotsPackSlot c = s ↔ a ≤ c ∧ c < a + len) → s < 5 →
      a + len ≤ 128 → 4 ^ len < goldilocksPrime → wotsPackSlotStart s = a →
      ∀ c, a ≤ c → c < a + len →
        stepChainDigit R (stepChainRow (tD + 5) c) = stepDigit hm c := by
    intro s a len hRange hs haN hLen hStart c hac hcl
    have h1 := hSlots s a len hRange hs haN hLen
    have h2 := hPack s (by omega)
    rw [stepPackFold_slot _ s a len hRange haN hStart] at h2
    rw [h2] at h1
    have hLtD : ∀ x ∈ (List.range' a len).map (fun c => 3 - stepDigit hm c), x < 4 := by
      intro x hx
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
      show 3 - stepDigit hm c' < 4
      omega
    have hLtd : ∀ x ∈ (List.range' a len).map
        (fun c => 3 - stepChainDigit R (stepChainRow (tD + 5) c)), x < 4 := by
      intro x hx
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
      show 3 - stepChainDigit R (stepChainRow (tD + 5) c') < 4
      omega
    have hBound := evalBaseDigits_lt_pow 4 (by decide) _ hLtD
    rw [List.length_map, List.length_range'] at hBound
    rw [Goldilocks.ofNat_val, Nat.mod_eq_of_lt (Nat.lt_trans hBound hLen)] at h1
    have hList := evalBaseDigits_inj 4 (by decide)
      (by rw [List.length_map, List.length_map]) hLtD hLtd h1
    have hc : 3 - stepDigit hm c = 3 - stepChainDigit R (stepChainRow (tD + 5) c) :=
      (List.map_inj_left.mp hList) c (mem_range'_of_bounds len a c hac hcl)
    have hd1 := hd c (by omega)
    have hd2 := stepDigit_le hm c
    omega
  have hDigAll : ∀ c < 128, stepChainDigit R (stepChainRow (tD + 5) c) = stepDigit hm c := by
    intro c hc
    by_cases h0 : c < 26
    · exact hDigEq 0 0 26 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
    by_cases h1 : c < 52
    · exact hDigEq 1 26 26 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
    by_cases h2 : c < 78
    · exact hDigEq 2 52 26 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
    by_cases h3 : c < 103
    · exact hDigEq 3 78 25 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
    · exact hDigEq 4 103 25 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
  have hEnd : stepLayerEndpoints pub R layer tree kpN (tD + 5) =
      recoverAggWotsEndpoints pub.1.pkSeed layer tree kpN 0
        ((List.range' 0 128).map (stepDigit hm)) (stepLayerChains R (tD + 5)) := by
    unfold stepLayerEndpoints stepLayerChains
    rw [List.range_eq_range', recoverAggWotsEndpoints_map]
    apply List.map_congr_left
    intro c hc
    have hb := mem_range'_bounds _ _ _ hc
    unfold stepChainEndpoint
    rw [hDigAll c (by omega)]
  have hLv : ∀ l < h, StepRunAt pub R
      [StepOp.xmssMerkleBlockA layer l,
       StepOp.xmssMerkleBlockB (l + 1 == h) ((l + 1 == h) && isTop)] (tD + 455 + l * 2) :=
    StepRunAt.flatMap_range (L := 2) (fun _ => rfl) h hM
  have hA : ∀ l < h, StepRowSem pub R (.xmssMerkleBlockA layer l) (tD + 455 + 2 * l) := by
    intro l hl'
    have h' := (hLv l hl').head
    rw [Nat.mul_comm l 2] at h'
    exact h'
  have hB : ∀ l < h, StepRowSem pub R
      (.xmssMerkleBlockB (l + 1 == h) ((l + 1 == h) && isTop)) (tD + 455 + 2 * l + 1) := by
    intro l hl'
    have h' := (hLv l hl').tail.head
    rw [Nat.mul_comm l 2] at h'
    exact h'
  have hBin : ∀ l < h, (R (tD + 455 + 2 * l + 1)).stIn =
      stepMerkleBIn (stepRegsAt R (tD + 455 + 2 * l + 1)) := by
    intro l hl'
    by_cases hlast : l + 1 < h
    · have hb : (l + 1 == h) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hB' := hB l hl'
      rw [hb] at hB'
      exact (stepSem_xmssMerkleBlockB_inner hB').1
    · have e : l = h - 1 := by omega
      rw [e]
      exact hLastIn
  have hBnext : ∀ l, l + 1 < h → stepRegsAt R (tD + 455 + 2 * l + 2) =
      { stepRegsAt R (tD + 455 + 2 * l + 1) with
        work := (stepPermAt R (tD + 455 + 2 * l + 1)).b0 } := by
    intro l hl'
    have hb : (l + 1 == h) = false := beq_eq_false_iff_ne.mpr (by omega)
    have hB' := hB l (by omega)
    rw [hb] at hB'
    exact (stepSem_xmssMerkleBlockB_inner hB').2
  obtain ⟨hKpLt, hWalk, hFr⟩ :=
    stepMerkle_sem (tag := domainMerkleNode)
      (M := fun l => ‹layer * 2 ^ 48 + (l + 1) * 2 ^ 32›) (layerV := layer) (treeV := tree)
      (addr := xmssNodeAddr) (fun l hl' => stepMerkleARow_xmss (hA l hl')) hBin hBnext hLastCur
      hCursor hk hh hh28 (fun l hl' _ L Rr => by
        rw [hAddr450.lo, hAddr450.hi]
        exact stepNodeHashF_xmss _ _ _ _ _ _ _ (by omega) (by omega)
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans hk (by decide))))
  refine ⟨hKpLt, ?_, hFr.curRoot.trans (hCur450R.trans hCR),
    ⟨hFr.kp.trans hAddr450.kp, hFr.treeLo.trans hAddr450.lo, hFr.treeHi.trans hAddr450.hi⟩⟩
  have hLen1 : (stepLayerChains R (tD + 5)).length = 128 := by
    unfold stepLayerChains
    rw [List.length_map, List.length_range]
  have hLen2 : (stepLayerPath R (tD + 455) h).length = h := by
    unfold stepLayerPath
    rw [List.length_map, List.length_range]
  unfold verifyWotsLayer
  simp only [hLen1, hLen2, hw, hsh, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    stepDigits_extract geom hm hw hChk, hSum, hts]
  rw [← hEnd, ← hWork]
  exact congrArg some hWalk

/-! ### §3.13. Active `XmssPoseidon2` slot: an accepted table yields a native signature -/

/-- `Σ_{i < n} (f i).val * w i`, the integer read off a weighted sum of cells. -/
def stepWeightedNat (f : Nat → Goldilocks) (w : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + (f i).val * w i) 0

private theorem stepWeightedSum_fold (f : Nat → Goldilocks) (w : Nat → Nat) :
    ∀ (is : List Nat) (A : Nat),
      is.foldl (fun acc i => acc +ₚ (f i *ₚ ‹w i›)) ‹A› =
        ‹is.foldl (fun acc i => acc + (f i).val * w i) A›
  | [], _ => rfl
  | i :: rest, A => by
    have hStep : (‹A› : Goldilocks) +ₚ (f i *ₚ ‹w i›) = ‹A + (f i).val * w i› := by
      rw [g_ofNat_add, g_ofNat_mul, g_ofNat_self]
    rw [List.foldl_cons, List.foldl_cons, hStep]
    exact stepWeightedSum_fold f w rest _

theorem stepWeightedSum_eq_ofNat (f : Nat → Goldilocks) (w : Nat → Nat) (n : Nat) :
    stepWeightedSum f w n = ‹stepWeightedNat f w n› :=
  stepWeightedSum_fold f w (List.range n) 0

private theorem stepWeightedNat_succ (f : Nat → Goldilocks) (w : Nat → Nat) (n : Nat) :
    stepWeightedNat f w (n + 1) = stepWeightedNat f w n + (f n).val * w n := by
  unfold stepWeightedNat
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem stepWeightedNat_bits_lt (f : Nat → Goldilocks) :
    ∀ (n : Nat), (∀ i < n, f i = Goldilocks.zero ∨ f i = Goldilocks.one) →
      stepWeightedNat f (fun i => 2 ^ i) n < 2 ^ n
  | 0, _ => Nat.le_of_ble_eq_true rfl
  | n + 1, h => by
    have ih := stepWeightedNat_bits_lt f n (fun i hi => h i (by omega))
    have hb : (f n).val ≤ 1 := by
      rcases h n (by omega) with hb | hb <;> rw [hb] <;> decide
    have hm : (f n).val * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ hb
    rw [stepWeightedNat_succ, Nat.pow_succ]
    omega

theorem verifyUpperLayers_nil (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer rem : Nat) (root : Digest4) :
    verifyUpperLayers geom pk layer rem root [] = some root := by
  rfl

/-- A stateful single-layer signature is accepted once its layer verifies to the root. -/
theorem verifyAggNativeSig_stateful_intro (geom : AggSigGeometry) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (leaf : Nat) (lsig0 : WotsLayerSig)
    (hWf : geom.wellFormed = true) (hPk : pk.profile = geom.profile)
    (hNL : geom.numLayers = 1) (hF : geom.forsTrees = 0)
    (hLeaf : leaf < 2 ^ (geom.numLayers * geom.subtreeHeight))
    (hV : verifyWotsLayer geom pk 0 (leaf / 2 ^ geom.subtreeHeight)
        (leaf % 2 ^ geom.subtreeHeight)
        (computeHmsgStateful pk rRand (computeMessageMu pk msg)
          (leaf % 2 ^ geom.subtreeHeight) lsig0.tswCtr) lsig0 = some pk.pkRoot) :
    verifyAggNativeSig geom pk msg ⟨geom.profile, rRand, leaf, [], [lsig0]⟩ = true := by
  have hCond : (!geom.wellFormed || pk.profile != geom.profile ||
      geom.profile != geom.profile || ([lsig0].length != geom.numLayers)) = false := by
    rw [hWf, hPk, hNL]
    simp
  have hDec : (!([] : List AggForsTreeOpening).isEmpty ||
      !decide (leaf < 2 ^ (geom.numLayers * geom.subtreeHeight))) = false := by
    simp [hLeaf]
  unfold verifyAggNativeSig
  simp only [hCond, Bool.false_eq_true, ↓reduceIte, hF, beq_self_eq_true]
  unfold verifyAggNativeSigStateful
  simp only [hDec, Bool.false_eq_true, ↓reduceIte, hV, verifyUpperLayers_nil, beq_self_eq_true]

/-- The native signature read from the auxiliary columns of an `XmssPoseidon2` signer block:
    `rRand` from the `StatefulHmsgBlock1` row, the leaf index and counter bits from the
    `StatefulHmsgBlock0` row, the chain values from the `WotsChainStep0` rows and the
    authentication path from the `XmssMerkleBlockA` rows. -/
def stepXmssSig (R : Nat → StepOpRow) : AggNativeSignature :=
  { profile := .xmssPoseidon2
    rRand := stepAuxLane R 1 0
    statefulLeafIdx := stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6
    forsOpenings := []
    layers :=
      [⟨stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32,
        stepLayerChains R 8, stepLayerPath R 458 6⟩] }

/-- **Native-signature witness extraction, `XmssPoseidon2` profile.** If the 256-column `StepOp`
    table is accepted and slot `k` is active with public inputs `(pk, mu)`, `mu` the message
    representative of `msg` under `pk`, then the signature read from the auxiliary columns of
    the slot's rows is accepted by the native verifier. -/
theorem stepOp256TableOk_xmss_extract (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hTable : stepOp256TableOk .xmssPoseidon2 slots rows = true)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .xmssPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    verifyAggNativeSig xmssPoseidon2Geom pub.1 msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows k)) = true := by
  obtain ⟨R, hR⟩ : ∃ R, R = stepOpSlotRow .xmssPoseidon2 rows k := ⟨_, rfl⟩
  rw [← hR]
  have hRun0 := stepOp256TableOk_slot_run .xmssPoseidon2 slots rows k pub hTable hSlot
  rw [← hR] at hRun0
  have hInit := stepOp256TableOk_slot_init .xmssPoseidon2 slots rows k pub hTable hSlot
  rw [← hR] at hInit
  have hRun : StepRunAt pub R
      (([StepOp.statefulHmsgBlock0, StepOp.statefulHmsgBlock1, StepOp.statefulHmsgSqueeze] ++
        (List.range 5).map StepOp.hmsgDecompLimb) ++ pushLayerWotsAndMerkle 0 6 true) 0 := hRun0
  have h0 : StepRowSem pub R .statefulHmsgBlock0 0 := hRun.append_left.append_left.head
  have h1 : StepRowSem pub R .statefulHmsgBlock1 1 := hRun.append_left.append_left.tail.head
  have h2 : StepRowSem pub R .statefulHmsgSqueeze 2 :=
    hRun.append_left.append_left.tail.tail.head
  have hDec : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) 3 :=
    hRun.append_left.append_right
  have hLayer : StepRunAt pub R (pushLayerWotsAndMerkle 0 6 true) (3 + 5) := hRun.append_right
  have hTop : StepRowSem pub R (.xmssMerkleBlockB true true) 469 :=
    hRun0 469 (by rw [buildSignerProgram_length.1]; decide)
  obtain ⟨hb6, hb32, hIn0, hR1⟩ := stepSem_statefulHmsgBlock0 h0
  obtain ⟨hIn1, hR2⟩ := stepSem_statefulHmsgBlock1 h1
  obtain ⟨hIn2, hR3⟩ := stepSem_statefulHmsgSqueeze h2
  have hR1' : stepRegsAt R 1 = _ := hR1
  have hR2' : stepRegsAt R 2 = _ := hR2
  have hR3' : stepRegsAt R 3 = _ := hR3
  obtain ⟨hLastIn, hLastCur, hRoot⟩ := stepSem_xmssMerkleBlockB_top hTop
  have hKp6 := stepWeightedNat_bits_lt (stepAux R 0) 6 hb6
  have hCtr := stepWeightedNat_bits_lt (fun i => stepAux R 0 (6 + i)) 32 hb32
  have hRem0 : ∀ s < 6, (stepRegsAt R 3).rem.get s = Goldilocks.zero := by
    intro s hs
    rw [hR3']
    rcases s with _ | _ | _ | _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hs (by omega)
  have hAcc0 : (stepRegsAt R 3).acc = Goldilocks.zero := by rw [hR3']
  have hAddr : StepAddrOk (stepRegsAt R 3)
      (stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6) 0 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hR3', hR2', hR1']
      exact stepWeightedSum_eq_ofNat _ _ _
    · rw [hR3', hR2', hR1']
      exact Goldilocks.ext rfl
    · rw [hR3', hR2', hR1']
      exact Goldilocks.ext rfl
  have hHm : stepHmsgOf (stepRegsAt R 3).main =
      computeHmsgStateful pub.1 (stepAuxLane R 1 0) pub.2
        (stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6)
        (stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32) := by
    have hKpCtr : (stepWeightedSum (stepAux R 0) (fun i => 2 ^ i) 6 *ₚ ‹2 ^ 32›) +ₚ
        stepWeightedSum (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32 =
        ‹(stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6 % 2 ^ 32) * 2 ^ 32 +
          stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32 % 2 ^ 32› := by
      rw [stepWeightedSum_eq_ofNat, stepWeightedSum_eq_ofNat, ← g_ofNat_mul, ← g_ofNat_add,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hCtr]
    have hM1 : (stepRegsAt R 1).main = poseidon2Perm12 (R 0).stIn := by rw [hR1']; rfl
    have hM2 : (stepRegsAt R 2).main = poseidon2Perm12 (R 1).stIn := by rw [hR2']; rfl
    have hM3 : (stepRegsAt R 3).main = poseidon2Perm12 (R 2).stIn := by rw [hR3']; rfl
    rw [hM3, hIn2]
    unfold stepSqueezeIn
    rw [hM2, hIn1, hM1, hIn0, hKpCtr]
    rfl
  obtain ⟨hKpLt, hV, _, _⟩ := stepLayer_verify (geom := xmssPoseidon2Geom) (layer := 0) (h := 6)
    (ctr := stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32)
    hDec hLayer hRem0 hAcc0 hAddr hLastIn hLastCur (by decide) (by omega) (by decide) (by decide)
    rfl rfl rfl
  rw [hHm, hMu] at hV
  have hV' : verifyWotsLayer xmssPoseidon2Geom pub.1 0 0
      (stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6)
      (computeHmsgStateful pub.1 (stepAuxLane R 1 0) (computeMessageMu pub.1 msg)
        (stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6)
        (stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32))
      ⟨stepWeightedNat (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32,
        stepLayerChains R 8, stepLayerPath R 458 6⟩ = some pub.1.pkRoot := by
    rw [← hRoot]
    exact hV
  have hDiv : stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6 /
      2 ^ xmssPoseidon2Geom.subtreeHeight = 0 := Nat.div_eq_of_lt hKp6
  have hMod : stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6 %
      2 ^ xmssPoseidon2Geom.subtreeHeight =
      stepWeightedNat (stepAux R 0) (fun i => 2 ^ i) 6 := Nat.mod_eq_of_lt hKp6
  exact verifyAggNativeSig_stateful_intro xmssPoseidon2Geom pub.1 msg _ _ _ (by decide) hProf
    rfl rfl hKp6 (by rw [hDiv, hMod]; exact hV')

/-! ### §3.14. Row semantics of the `CorduroyPoseidon2` opcodes -/

/-- The all-zero `ST_REM_PACK` block. -/
def stepRemZero : StepRem :=
  ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
    Goldilocks.zero⟩

theorem stepSem_statelessDeriveBlock0 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statelessDeriveBlock0 t) :
    (R t).stIn =
      ⟨pub.1.pkSeed, pub.1.pkRoot,
       ⟨domainHMsgStateless, pub.2.limb4, Goldilocks.zero, poseidon2IvTag⟩⟩ ∧
    stepRegsAt R (t + 1) =
      { curRoot := lane4Zero
        kp := Goldilocks.zero
        treeLo := Goldilocks.zero
        treeHi := Goldilocks.zero
        rem := stepRemZero
        main := stepPermAt R t
        sub := state12Zero
        work := lane4Zero
        cursor := Goldilocks.zero
        acc := Goldilocks.zero
        u2 := Goldilocks.zero } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gzz% hG 10) (gz% hG 11), h.regs⟩

theorem stepSem_statelessDeriveBlock1 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .statelessDeriveBlock1 t) :
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepAuxLane R t 0),
       lane4Add (stepRegsAt R t).main.b1 ⟨pub.2.limb0, pub.2.limb1, pub.2.limb2, pub.2.limb3⟩,
       (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with main := stepPermAt R t, rem := stepRemZero } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 3) (gz% hG 6) (gz% hG 9) (gz% hG 1) (gz% hG 4)
    (gz% hG 7) (gz% hG 10) (gz% hG 2) (gz% hG 5) (gz% hG 8) (gz% hG 11), h.regs⟩

/-- `StatelessDecompLimb l`, `l < 5`: the FORS index bytes of the limb are packed into
    `ST_REM_PACK`; nothing else changes. -/
theorem stepSem_statelessDecompLimb_pack {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {l t : Nat} (hl : l < 5) (h : StepRowSem pub R (.statelessDecompLimb l) t) :
    allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) l) = true ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := ⟨stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 7,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 8,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 9,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 10,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 11,
          stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l 12⟩ } := by
  have hG := h.guard
  rcases l with _ | _ | _ | _ | _ | l
  · exact ⟨hG, h.regs⟩
  · exact ⟨hG, h.regs⟩
  · exact ⟨hG, h.regs⟩
  · exact ⟨hG, h.regs⟩
  · exact ⟨hG, h.regs⟩
  · exact absurd hl (by omega)

/-- `StatelessDecompLimb 5`: the low 32 bits of the limb give `kp_idx` (4 bits) and the low
    28 bits of the tree index. -/
theorem stepSem_statelessDecompLimb5 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R (.statelessDecompLimb 5) t) :
    allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) 5) = true ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        kp := stepAux R t 0 +ₚ (stepAux R t 1 *ₚ ‹4›)
        treeLo := stepHi28 (stepOpRowInputsPerm pub (R t)) } :=
  ⟨h.guard, h.regs⟩

/-- `StatelessDecompLimb 6`: the low 32 bits of the limb give tree-index bits 28..59. -/
theorem stepSem_statelessDecompLimb6 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R (.statelessDecompLimb 6) t) :
    allZeroGoldilocks (stepLimb63Decomp (stepOpRowInputsPerm pub (R t)) 6) = true ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        treeLo := (stepRegsAt R t).treeLo +ₚ
          ((stepAux R t 0 +ₚ (stepAux R t 1 *ₚ ‹4›)) *ₚ ‹2 ^ 28›)
        treeHi := stepHi28 (stepOpRowInputsPerm pub (R t)) } :=
  ⟨h.guard, h.regs⟩

theorem stepSem_forsRootsSpongeInit {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .forsRootsSpongeInit t) :
    (R t).stIn =
      ⟨pub.1.pkSeed,
       ⟨(stepRegsAt R t).kp, (stepRegsAt R t).treeLo, (stepRegsAt R t).treeHi, ‹32›⟩,
       ⟨domainForsRoots, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gzz% hG 9) (gzz% hG 10) (gz% hG 11), h.regs⟩

/-- The FORS leaf index read from the four base-4 digits `aux[4..8]`. -/
def stepForsIdxF (R : Nat → StepOpRow) (t : Nat) : Goldilocks :=
  stepWeightedSum (fun k => stepAux R t (4 + k)) (fun k => 4 ^ k) 4

theorem stepSem_forsLeafHash {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {j slot t : Nat} (hs : slot < 6) (h : StepRowSem pub R (.forsLeafHash j slot) t) :
    (∀ k < 4, (stepAux R t (4 + k)).val < 4) ∧
    (stepRegsAt R t).rem.get slot = stepForsIdxF R t +ₚ (stepAux R t 8 *ₚ ‹256›) ∧
    (R t).stIn =
      ⟨stepAuxLane R t 0, pub.1.pkSeed,
       ⟨domainForsLeaf,
        ((stepRegsAt R t).kp *ₚ ‹2 ^ 24›) +ₚ (‹j * 2 ^ 8› +ₚ stepForsIdxF R t),
        (stepRegsAt R t).treeLo, (stepRegsAt R t).treeHi⟩⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := (stepRegsAt R t).rem.set slot (stepAux R t 8)
        work := lane4Add (stepPermAt R t).b0 (stepAuxLane R t 0)
        cursor := stepForsIdxF R t } := by
  have hG := h.guard
  have hQ : allZeroGoldilocks ((List.range 4).map
      (fun k => quarticBase4 (stepAux R t (4 + k)))) = true := allZero_take hG 4
  have hQ' : ∀ k < 4, (stepAux R t (4 + k)).val < 4 := fun k hk =>
    (quarticBase4_eq_zero_iff _).mp ((allZero_map_iff 4 _).mp hQ k hk)
  rcases slot with _ | _ | _ | _ | _ | _ | slot
  all_goals first
    | exact ⟨hQ', gz% hG 4,
        state12_ext12 (gz% hG 5) (gz% hG 7) (gz% hG 9) (gz% hG 11) (gz% hG 6) (gz% hG 8)
          (gz% hG 10) (gz% hG 12) (gz% hG 13) (gz% hG 14) (gz% hG 15) (gz% hG 16), h.regs⟩
    | exact absurd hs (by omega)

theorem stepMerkleARow_fors {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {j lvl t : Nat} (h : StepRowSem pub R (.forsMerkleBlockA j lvl) t) :
    StepMerkleARow pub R t domainForsNode
      (‹(lvl + 1) * 2 ^ 32 + j * 2 ^ (7 - lvl)› +ₚ ((stepRegsAt R t).kp *ₚ ‹2 ^ 16›)) := by
  have hG := h.guard
  exact ⟨(stepBoolCheck_eq_zero_iff _).mp (gzz% hG 0), gz% hG 1,
    state12_ext12 (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 8) (gz% hG 3) (gz% hG 5)
      (gz% hG 7) (gz% hG 9) (gz% hG 10) (gz% hG 11) (gz% hG 12) (gz% hG 13), h.regs⟩

theorem stepSem_forsMerkleBlockB_inner {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {lvl : Nat} {isOdd : Bool} {t : Nat}
    (h : StepRowSem pub R (.forsMerkleBlockB lvl false isOdd) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with work := (stepPermAt R t).b0 } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), h.regs⟩

theorem stepSem_forsMerkleBlockB_even {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {lvl t : Nat} (h : StepRowSem pub R (.forsMerkleBlockB lvl true false) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    (stepRegsAt R t).cursor = Goldilocks.zero ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with curRoot := (stepPermAt R t).b0 } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), gzz% hG 12, h.regs⟩

theorem stepSem_forsMerkleBlockB_odd {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {lvl t : Nat} (h : StepRowSem pub R (.forsMerkleBlockB lvl true true) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    (stepRegsAt R t).cursor = Goldilocks.zero ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with work := (stepPermAt R t).b0 } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), gzz% hG 12, h.regs⟩

theorem stepSem_forsRootsPairAbsorb {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {pair t : Nat} (h : StepRowSem pub R (.forsRootsPairAbsorb pair) t) :
    ((pair + 1 == 16) = true → ∀ s < 6, (stepRegsAt R t).rem.get s = Goldilocks.zero) ∧
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepRegsAt R t).curRoot,
       lane4Add (stepRegsAt R t).main.b1 (stepRegsAt R t).work, (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG : allZeroGoldilocks (stepOpGuardResiduals (.forsRootsPairAbsorb (pair + 1 == 16))
      (Goldilocks.ofNat 0) (stepOpRowInputsPerm pub (R t))) = true := h.guard
  cases hp : (pair + 1 == 16)
  · rw [hp] at hG
    exact ⟨fun hc => absurd hc (by simp),
      state12_ext12 (gz% hG 0) (gz% hG 3) (gz% hG 6) (gz% hG 9) (gz% hG 1) (gz% hG 4)
        (gz% hG 7) (gz% hG 10) (gz% hG 2) (gz% hG 5) (gz% hG 8) (gz% hG 11), h.regs⟩
  · rw [hp] at hG
    refine ⟨fun _ s hs => ?_,
      state12_ext12 (gz% hG 6) (gz% hG 9) (gz% hG 12) (gz% hG 15) (gz% hG 7) (gz% hG 10)
        (gz% hG 13) (gz% hG 16) (gz% hG 8) (gz% hG 11) (gz% hG 14) (gz% hG 17), h.regs⟩
    rcases s with _ | _ | _ | _ | _ | _ | s
    · exact gzz% hG 0
    · exact gzz% hG 1
    · exact gzz% hG 2
    · exact gzz% hG 3
    · exact gzz% hG 4
    · exact gzz% hG 5
    · exact absurd hs (by omega)

theorem stepSem_forsRootsFinalSqueeze {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R .forsRootsFinalSqueeze t) :
    (R t).stIn = stepSqueezeIn (stepRegsAt R t) ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with curRoot := (stepPermAt R t).b0 } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
    (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), h.regs⟩

theorem stepSem_detTreeHmsgBlock0 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer t : Nat} (h : StepRowSem pub R (.detTreeHmsgBlock0 layer) t) :
    (R t).stIn =
      ⟨pub.1.pkSeed, pub.1.pkRoot,
       ⟨domainHMsgDetTree, ‹layer * 2 ^ 32› +ₚ (stepRegsAt R t).kp, (stepRegsAt R t).treeLo,
        (stepRegsAt R t).treeHi⟩⟩ ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with main := stepPermAt R t } := by
  have hG := h.guard
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 2) (gz% hG 4) (gz% hG 6) (gz% hG 1) (gz% hG 3)
    (gz% hG 5) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), h.regs⟩

theorem stepSem_detTreeHmsgBlock1 {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer t : Nat} (h : StepRowSem pub R (.detTreeHmsgBlock1 layer) t) :
    (∀ i < 32, stepAux R t i = Goldilocks.zero ∨ stepAux R t i = Goldilocks.one) ∧
    (R t).stIn =
      ⟨lane4Add (stepRegsAt R t).main.b0 (stepRegsAt R t).curRoot,
       ⟨(stepRegsAt R t).main.b1.x0 +ₚ stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 32,
        (stepRegsAt R t).main.b1.x1 +ₚ Goldilocks.one,
        (stepRegsAt R t).main.b1.x2, (stepRegsAt R t).main.b1.x3⟩,
       (stepRegsAt R t).main.b2⟩ ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        rem := stepRemZero
        main := stepPermAt R t
        acc := Goldilocks.zero } := by
  have hG := h.guard
  have hB : allZeroGoldilocks ((List.range 32).map
      (fun i => stepBoolCheck (stepAux R t i))) = true := allZero_take hG 32
  exact ⟨fun i hi => (stepBoolCheck_eq_zero_iff _).mp ((allZero_map_iff 32 _).mp hB i hi),
    state12_ext12 (gz% hG 32) (gz% hG 33) (gz% hG 34) (gz% hG 35) (gz% hG 36) (gz% hG 37)
      (gz% hG 38) (gz% hG 39) (gz% hG 40) (gz% hG 41) (gz% hG 42) (gz% hG 43), h.regs⟩

/-- `XmssMerkleBlockB` closing a non-top layer: the layer root moves to `ST_CUR_ROOT` and the
    64-bit tree index is shifted right by the subtree height (4 bits) into `kp_idx`. -/
theorem stepSem_xmssMerkleBlockB_link {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {t : Nat} (h : StepRowSem pub R (.xmssMerkleBlockB true false) t) :
    (R t).stIn = stepMerkleBIn (stepRegsAt R t) ∧
    (stepRegsAt R t).cursor = Goldilocks.zero ∧
    (∀ i < 4, stepAux R t i = Goldilocks.zero ∨ stepAux R t i = Goldilocks.one) ∧
    (∀ i < 14, (stepAux R t (4 + i)).val < 4) ∧
    (∀ i < 2, (stepAux R t (18 + i)).val < 4) ∧
    (∀ i < 14, (stepAux R t (20 + i)).val < 4) ∧
    (stepRegsAt R t).treeLo =
      stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 4 +ₚ
        (stepWeightedSum (fun i => stepAux R t (4 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›) ∧
    (stepRegsAt R t).treeHi =
      stepWeightedSum (fun i => stepAux R t (18 + i)) (fun i => 4 ^ i) 2 +ₚ
        (stepWeightedSum (fun i => stepAux R t (20 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›) ∧
    stepRegsAt R (t + 1) =
      { stepRegsAt R t with
        curRoot := (stepPermAt R t).b0
        kp := stepWeightedSum (stepAux R t) (fun i => 2 ^ i) 4
        treeLo := stepWeightedSum (fun i => stepAux R t (4 + i)) (fun i => 4 ^ i) 14 +ₚ
          (stepWeightedSum (fun i => stepAux R t (18 + i)) (fun i => 4 ^ i) 2 *ₚ ‹2 ^ 28›)
        treeHi := stepWeightedSum (fun i => stepAux R t (20 + i)) (fun i => 4 ^ i) 14 } := by
  have hG := h.guard
  have hB4 : allZeroGoldilocks ((List.range 4).map
      (fun i => stepBoolCheck (stepAux R t i))) = true := allZero_take (allZero_drop hG 13) 4
  have hQa : allZeroGoldilocks ((List.range 14).map
      (fun i => quarticBase4 (stepAux R t (4 + i)))) = true := allZero_take (allZero_drop hG 17) 14
  have hQ2 : allZeroGoldilocks ((List.range 2).map
      (fun i => quarticBase4 (stepAux R t (18 + i)))) = true := allZero_take (allZero_drop hG 31) 2
  have hQb : allZeroGoldilocks ((List.range 14).map
      (fun i => quarticBase4 (stepAux R t (20 + i)))) = true := allZero_take (allZero_drop hG 33) 14
  exact ⟨state12_ext12 (gz% hG 0) (gz% hG 1) (gz% hG 2) (gz% hG 3) (gz% hG 4) (gz% hG 5)
      (gz% hG 6) (gz% hG 7) (gz% hG 8) (gz% hG 9) (gz% hG 10) (gz% hG 11), gzz% hG 12,
    fun i hi => (stepBoolCheck_eq_zero_iff _).mp ((allZero_map_iff 4 _).mp hB4 i hi),
    fun i hi => (quarticBase4_eq_zero_iff _).mp ((allZero_map_iff 14 _).mp hQa i hi),
    fun i hi => (quarticBase4_eq_zero_iff _).mp ((allZero_map_iff 2 _).mp hQ2 i hi),
    fun i hi => (quarticBase4_eq_zero_iff _).mp ((allZero_map_iff 14 _).mp hQb i hi),
    gz% hG 47, gz% hG 48, h.regs⟩


/-- Executable decision and witness extraction for an active XMSS slot. The success branch
    contains the native signature itself, not an existential proposition requiring choice. -/
def extractXmssSlotOrReject (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .xmssPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    PSum { sig : AggNativeSignature // verifyAggNativeSig xmssPoseidon2Geom pub.1 msg sig = true }
      (stepOp256TableOk .xmssPoseidon2 slots rows = false) :=
  if h : stepOp256TableOk .xmssPoseidon2 slots rows = true then
    .inl ⟨stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows k),
      stepOp256TableOk_xmss_extract slots rows k pub msg h hSlot hProf hMu⟩
  else .inr (Bool.eq_false_iff.mpr h)

/-- The active slots for a public committee statement bind both key and message digest. -/
def xmssCommitteeSlots (stmt : AggArithPublicStmt) : List StepOpSlot :=
  stmt.committeePks.map (fun pk => some (pk, computeMessageMu pk stmt.msg))

/-- Read every signature from its accepted machine block in committee order. -/
def xmssCommitteeSigs (stmt : AggArithPublicStmt) (rows : List StepOpRow) :
    List AggNativeSignature :=
  (List.range stmt.committeePks.length).map
    (fun k => stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows k))

/-- Whole-committee soundness of the XMSS machine extractor. -/
theorem xmssCommitteeSigs_valid (stmt : AggArithPublicStmt) (rows : List StepOpRow)
    (hGeom : stmt.geom = xmssPoseidon2Geom) (hWf : stmt.wellFormed = true)
    (hTable : stepOp256TableOk .xmssPoseidon2 (xmssCommitteeSlots stmt) rows = true) :
    (xmssCommitteeSigs stmt rows).length = stmt.committeePks.length ∧
    ∀ (k : Nat) (hkP : k < stmt.committeePks.length)
      (hkS : k < (xmssCommitteeSigs stmt rows).length),
      verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
        ((xmssCommitteeSigs stmt rows)[k]'hkS) = true := by
  refine ⟨by simp [xmssCommitteeSigs], ?_⟩
  intro k hkP hkS
  have hpks : stmt.committeePks.all (·.profile == stmt.geom.profile) = true :=
    (Bool.and_eq_true_iff.mp hWf).2
  have hp : (stmt.committeePks[k]'hkP).profile = .xmssPoseidon2 := by
    have h := eq_of_beq (List.all_eq_true.mp hpks _ (List.getElem_mem hkP))
    simpa only [hGeom, xmssPoseidon2Geom] using h
  have hs : (xmssCommitteeSlots stmt)[k]? =
      some (some (stmt.committeePks[k]'hkP, computeMessageMu (stmt.committeePks[k]'hkP) stmt.msg)) := by
    simp [xmssCommitteeSlots, List.getElem?_eq_getElem hkP]
  simpa [xmssCommitteeSigs, hGeom] using
    stepOp256TableOk_xmss_extract (xmssCommitteeSlots stmt) rows k
      (stmt.committeePks[k]'hkP, computeMessageMu (stmt.committeePks[k]'hkP) stmt.msg)
      stmt.msg hTable hs hp rfl

/-- Construct the serialized trace from the machine-extracted signatures. Its 14 boundary
    columns and serialized witness blocks are checked by the existing row constraints. -/
def xmssMachineToExecutionTrace (stmt : AggArithPublicStmt) (rows : List StepOpRow) :
    AggExecutionTrace := buildHonestAggExecutionTrace stmt (xmssCommitteeSigs stmt rows)

theorem xmssMachineToExecutionTrace_accepts (stmt : AggArithPublicStmt) (rows : List StepOpRow)
    (hGeom : stmt.geom = xmssPoseidon2Geom) (hWf : stmt.wellFormed = true)
    (hTable : stepOp256TableOk .xmssPoseidon2 (xmssCommitteeSlots stmt) rows = true) :
    traceSatisfiesAllConstraints stmt (xmssMachineToExecutionTrace stmt rows) = true := by
  obtain ⟨hLen, hAll⟩ := xmssCommitteeSigs_valid stmt rows hGeom hWf hTable
  exact buildHonestAggExecutionTrace_satisfies_constraints stmt _ hWf hLen hAll


/-! ### §3.15. Stateless derive rows: FORS indices and the 64-bit leaf index -/

/-- Row `t0 + i` of a run executes the `i`-th opcode of the run. -/
private theorem StepRunAt.get {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {ops : List StepOp} {t0 : Nat} (h : StepRunAt pub R ops t0) (i : Nat) (op : StepOp)
    (hop : ops[i]? = some op) : StepRowSem pub R op (t0 + i) := by
  obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hop
  have h' := h i hi
  rw [he] at h'
  exact h'

private theorem g_ofNat_inj {a b : Nat} (ha : a < goldilocksPrime) (hb : b < goldilocksPrime)
    (h : (‹a› : Goldilocks) = ‹b›) : a = b := by
  have hv := congrArg Goldilocks.val h
  rw [Goldilocks.ofNat_val, Goldilocks.ofNat_val, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  exact hv

/-- Four consecutive base-4 digits are one base-256 digit. -/
private theorem nat_byte_of_quads (v s : Nat) :
    (v / 4 ^ (4 * s)) % 4 + (v / 4 ^ (4 * s + 1)) % 4 * 4 + (v / 4 ^ (4 * s + 2)) % 4 * 16 +
      (v / 4 ^ (4 * s + 3)) % 4 * 64 = (v / 256 ^ s) % 256 := by
  have e0 : 4 ^ (4 * s) = 256 ^ s := by rw [Nat.pow_mul]
  have e1 : v / 4 ^ (4 * s + 1) = v / 256 ^ s / 4 := by
    rw [Nat.pow_succ, e0, Nat.div_div_eq_div_mul]
  have e2 : v / 4 ^ (4 * s + 2) = v / 256 ^ s / 16 := by
    rw [Nat.pow_add, e0, Nat.div_div_eq_div_mul]
  have e3 : v / 4 ^ (4 * s + 3) = v / 256 ^ s / 64 := by
    rw [Nat.pow_add, e0, Nat.div_div_eq_div_mul]
  rw [e0, e1, e2, e3]
  generalize v / 256 ^ s = w
  omega

/-- A weighted sum of the low `n` base-`B` digits of `w` is `w` without its high part. -/
private theorem stepWeightedNat_digits (B w : Nat) (f : Nat → Goldilocks)
    (hB : B ≤ goldilocksPrime) (hB0 : 0 < B) :
    ∀ n, (∀ i < n, f i = ‹(w / B ^ i) % B›) →
      stepWeightedNat f (fun i => B ^ i) n + B ^ n * (w / B ^ n) = w
  | 0, _ => by
    rw [Nat.pow_zero, Nat.div_one, Nat.one_mul]
    exact Nat.zero_add w
  | n + 1, h => by
    have ih := stepWeightedNat_digits B w f hB hB0 n (fun i hi => h i (by omega))
    have hd : (w / B ^ n) % B < goldilocksPrime :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ hB0) hB
    have hq := Nat.div_add_mod (w / B ^ n) B
    have key : w / B ^ n % B * B ^ n + B ^ n * B * (w / B ^ n / B) = B ^ n * (w / B ^ n) := by
      rw [Nat.mul_comm (w / B ^ n % B) (B ^ n), Nat.mul_assoc, ← Nat.mul_add, Nat.add_comm, hq]
    rw [stepWeightedNat_succ, h n (by omega), Goldilocks.ofNat_val, Nat.mod_eq_of_lt hd,
      Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_assoc, key]
    exact ih

/-- A weighted sum of `n` base-`B` digits is below `B ^ n`. -/
private theorem stepWeightedNat_lt (B : Nat) (f : Nat → Goldilocks) :
    ∀ n, (∀ i < n, (f i).val < B) → stepWeightedNat f (fun i => B ^ i) n < B ^ n
  | 0, _ => Nat.le_of_ble_eq_true rfl
  | n + 1, h => by
    have ih := stepWeightedNat_lt B f n (fun i hi => h i (by omega))
    have hd := h n (by omega)
    have h1 : ((f n).val + 1) * B ^ n ≤ B * B ^ n := Nat.mul_le_mul_right _ hd
    rw [Nat.succ_mul] at h1
    rw [stepWeightedNat_succ, Nat.pow_succ, Nat.mul_comm (B ^ n) B]
    omega

/-- Limb `l` of the seven limbs the stateless XOF squeezes. -/
def stepXofLimb (m : Poseidon2State12) : Nat → Goldilocks
  | 0 => m.b0.x0
  | 1 => m.b0.x1
  | 2 => m.b0.x2
  | 3 => m.b0.x3
  | 4 => m.b1.x0
  | 5 => m.b1.x1
  | _ => m.b1.x2

/-- FORS leaf index of tree `t`: byte `t % 7` of squeezed limb `t / 7`. -/
def stepForsIdx (m : Poseidon2State12) (t : Nat) : Nat :=
  ((stepXofLimb m (t / 7)).val / 256 ^ (t % 7)) % 256

private theorem stepForsIdx_lt (m : Poseidon2State12) (t : Nat) : stepForsIdx m t < 256 :=
  Nat.mod_lt _ (by decide)

/-- The 64-bit global leaf index: the low 32 bits of limbs 5 and 6. -/
def stepXofLeaf (m : Poseidon2State12) : Nat :=
  (m.b1.x1.val % 2 ^ 32) + (m.b1.x2.val % 2 ^ 32) * 2 ^ 32

/-- The stateless XOF state of a signer block: `rRand` is read from the auxiliary cells of
    the `StatelessDeriveBlock1` row. -/
def stepXofState (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow) : Poseidon2State12 :=
  statelessXofSpongeState pub.1 (stepAuxLane R 1 0) pub.2

/-- The FORS packing fold of a `StatelessDecompLimb` row computes the base-256 packing of the
    bytes it reads. -/
private theorem stepForsPack_field (x : StepOpRowInputs) (bv : Nat → Nat) (firstJ s : Nat) :
    ∀ (subs : List Nat) (A : Nat),
      (∀ sub ∈ subs, stepByteVal x sub = ‹bv (firstJ + sub)›) →
      subs.foldl (fun acc sub =>
          if stRemPack + (firstJ + sub) / 6 = stRemPack + s then
            acc +ₚ (stepByteVal x sub *ₚ ‹2 ^ (8 * ((firstJ + sub) % 6))›)
          else acc) ‹A› =
        ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') bv s
          (subs.map (fun sub => firstJ + sub)) A›
  | [], _, _ => rfl
  | sub :: rest, A, h => by
    have hB := h sub (List.mem_cons_self ..)
    have ih := fun A' => stepForsPack_field x bv firstJ s rest A'
      (fun j hj => h j (List.mem_cons_of_mem _ hj))
    rw [List.foldl_cons, List.map_cons]
    unfold stepPackFoldG
    rw [List.foldl_cons]
    by_cases hc : (firstJ + sub) / 6 = s
    · simp only [hc, ↓reduceIte]
      have hE : (firstJ + sub) % 6 = firstJ + sub - 6 * s := by omega
      have hStep : (‹A› : Goldilocks) +ₚ
          (stepByteVal x sub *ₚ ‹2 ^ (8 * ((firstJ + sub) % 6))›) =
          ‹A + bv (firstJ + sub) * 256 ^ (firstJ + sub - 6 * s)› := by
        rw [hB, ← g_ofNat_mul, ← g_ofNat_add, hE, Nat.pow_mul]
      rw [hStep]
      exact ih _
    · have hcond : ¬ (stRemPack + (firstJ + sub) / 6 = stRemPack + s) :=
        fun h' => hc (Nat.add_left_cancel h')
      simp only [hcond, hc, ↓reduceIte]
      exact ih _

private theorem stepForsIdx_eq (m : Poseidon2State12) (l sub : Nat) (hs : sub < 7) :
    stepForsIdx m (7 * l + sub) = ((stepXofLimb m l).val / 256 ^ sub) % 256 := by
  unfold stepForsIdx
  rw [show (7 * l + sub) / 7 = l by omega, show (7 * l + sub) % 7 = sub by omega]

/-- **`StatelessDecompLimb l` row, `l < 5`.** The limb is `< 2^63`, and its low bytes are added
    to the `ST_REM_PACK` limbs as the FORS indices of the trees it owns. -/
theorem stepStatelessPack_row {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow} {l t : Nat}
    (hl : l < 5) (h : StepRowSem pub R (.statelessDecompLimb l) t) (A : Nat → Nat)
    (hRem : ∀ s < 6, (stepRegsAt R t).rem.get s = ‹A s›) :
    (stepXofLimb (stepRegsAt R t).main l).val < 2 ^ 63 ∧
    (∀ s < 6, (stepRegsAt R (t + 1)).rem.get s =
      ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') (stepForsIdx (stepRegsAt R t).main) s
        (List.range' (7 * l) (if l < 4 then 7 else 4)) (A s)›) ∧
    stepRegsAt R (t + 1) = { stepRegsAt R t with rem := (stepRegsAt R (t + 1)).rem } := by
  obtain ⟨hD, hR⟩ := stepSem_statelessDecompLimb_pack hl h
  obtain ⟨hLt, hAux, _⟩ := (stepLimb63Decomp_allZero_iff _ l).mp hD
  have hLimb : (stepOpRowInputsPerm pub (R t)).prev (stMainSponge + l) =
      stepXofLimb (stepRegsAt R t).main l := by
    rcases l with _ | _ | _ | _ | _ | l
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hl (by omega)
  rw [hLimb] at hLt hAux
  have hByte : ∀ sub < 7, stepByteVal (stepOpRowInputsPerm pub (R t)) sub =
      ‹stepForsIdx (stepRegsAt R t).main (7 * l + sub)› := by
    intro sub hs
    unfold stepByteVal
    rw [hAux (4 * sub) (by omega), hAux (4 * sub + 1) (by omega), hAux (4 * sub + 2) (by omega),
      hAux (4 * sub + 3) (by omega), ← g_ofNat_mul, ← g_ofNat_mul, ← g_ofNat_mul, ← g_ofNat_add,
      ← g_ofNat_add, ← g_ofNat_add, stepForsIdx_eq _ l sub hs]
    exact congrArg Goldilocks.ofNat (nat_byte_of_quads _ _)
  have hRemE : ∀ s < 6,
      stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l (stRemPack + s) =
      ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') (stepForsIdx (stepRegsAt R t).main) s
        (List.range' (7 * l) (if l < 4 then 7 else 4)) (A s)› := by
    intro s hs
    have hPrev : (stepOpRowInputsPerm pub (R t)).prev (stRemPack + s) = ‹A s› := by
      rw [← hRem s hs]
      rcases s with _ | _ | _ | _ | _ | _ | s
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd hs (by omega)
    by_cases h4 : l < 4
    · unfold stepStatelessDecompExpected stepForsPackExpected
      simp only [h4, ↓reduceIte]
      rw [hPrev, range'_eq_map]
      exact stepForsPack_field _ _ (7 * l) s (List.range 7) (A s)
        (fun sub hsub => hByte sub (List.mem_range.mp hsub))
    · have e4 : l = 4 := by omega
      subst e4
      show stepForsPackExpected (stepOpRowInputsPerm pub (R t)) 28 4 (stRemPack + s) =
        ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') (stepForsIdx (stepRegsAt R t).main) s
          (List.range' 28 4) (A s)›
      unfold stepForsPackExpected
      rw [hPrev, range'_eq_map]
      exact stepForsPack_field _ _ 28 s (List.range 4) (A s)
        (fun sub hsub => hByte sub (by have := List.mem_range.mp hsub; omega))
  have hRemGet : ∀ s < 6, (stepRegsAt R (t + 1)).rem.get s =
      stepStatelessDecompExpected (stepOpRowInputsPerm pub (R t)) l (stRemPack + s) := by
    intro s hs
    rw [hR]
    rcases s with _ | _ | _ | _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hs (by omega)
  refine ⟨hLt, fun s hs => (hRemGet s hs).trans (hRemE s hs), ?_⟩
  rw [hR]

private theorem range'_32_split :
    List.range' 0 32 =
      List.range' 0 7 ++ List.range' 7 7 ++ List.range' 14 7 ++ List.range' 21 7 ++
        List.range' 28 4 := by
  decide

/-- The two low base-4 digits of a decomposed limb are its low four bits. -/
private theorem stepLow4_eq (x : StepOpRowInputs) (v : Nat)
    (hAux : ∀ i < 31, x.aux i = ‹(v / 4 ^ i) % 4›) :
    x.aux 0 +ₚ (x.aux 1 *ₚ ‹4›) = ‹v % 16› := by
  have a0 := hAux 0 (by decide)
  have a1 := hAux 1 (by decide)
  rw [Nat.pow_zero, Nat.div_one] at a0
  rw [Nat.pow_one] at a1
  rw [a0, a1, ← g_ofNat_mul, ← g_ofNat_add]
  exact congrArg Goldilocks.ofNat (by omega)

/-- Digits 2..15 of a decomposed limb are bits 4..31 of the limb. -/
private theorem stepHi28_eq (x : StepOpRowInputs) (v : Nat)
    (hAux : ∀ i < 31, x.aux i = ‹(v / 4 ^ i) % 4›) :
    stepHi28 x = ‹(v / 16) % 4 ^ 14› := by
  unfold stepHi28
  rw [stepWeightedSum_eq_ofNat]
  have hS := stepWeightedNat_digits 4 (v / 16) (fun i => x.aux (2 + i)) (by decide) (by decide)
    14 (fun i hi => by
      show x.aux (2 + i) = _
      rw [hAux (2 + i) (by omega), Nat.pow_add, Nat.div_div_eq_div_mul])
  have hL := stepWeightedNat_lt 4 (fun i => x.aux (2 + i)) 14 (fun i hi => by
    show (x.aux (2 + i)).val < 4
    rw [hAux (2 + i) (by omega), Goldilocks.ofNat_val]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide)))
  exact congrArg Goldilocks.ofNat (by omega)

/-- The nine rows of the stateless derive. -/
def stepDeriveOps : List StepOp :=
  [StepOp.statelessDeriveBlock0, StepOp.statelessDeriveBlock1] ++
    (List.range 7).map StepOp.statelessDecompLimb

/-- **Stateless derive rows.** The nine rows `StatelessDeriveBlock0 .. StatelessDecompLimb 6`
    check that the seven squeezed limbs of the stateless XOF are `< 2^63`, leave in each
    `ST_REM_PACK` limb the base-256 packing of the FORS indices of the trees it owns, and load
    the address registers with the split `(leaf % 16, leaf / 16)` of the global leaf index. -/
theorem stepStatelessDerive_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    (hRun : StepRunAt pub R stepDeriveOps 0) :
    (∀ l < 7, (stepXofLimb (stepXofState pub R) l).val < 2 ^ 63) ∧
    (∀ s < 6, (stepRegsAt R 9).rem.get s =
      ‹stepPackFoldG 256 (fun c => c / 6) (fun s' => 6 * s') (stepForsIdx (stepXofState pub R)) s
        (List.range' 0 32) 0›) ∧
    StepAddrOk (stepRegsAt R 9) (stepXofLeaf (stepXofState pub R) % 16)
      (stepXofLeaf (stepXofState pub R) / 16) := by
  have hz : (‹0› : Goldilocks) = Goldilocks.zero := Goldilocks.ext rfl
  have h0 : StepRowSem pub R .statelessDeriveBlock0 0 := hRun.get 0 _ rfl
  have h1 : StepRowSem pub R .statelessDeriveBlock1 1 := hRun.get 1 _ rfl
  have d0 : StepRowSem pub R (.statelessDecompLimb 0) 2 := hRun.get 2 _ rfl
  have d1 : StepRowSem pub R (.statelessDecompLimb 1) 3 := hRun.get 3 _ rfl
  have d2 : StepRowSem pub R (.statelessDecompLimb 2) 4 := hRun.get 4 _ rfl
  have d3 : StepRowSem pub R (.statelessDecompLimb 3) 5 := hRun.get 5 _ rfl
  have d4 : StepRowSem pub R (.statelessDecompLimb 4) 6 := hRun.get 6 _ rfl
  have d5 : StepRowSem pub R (.statelessDecompLimb 5) 7 := hRun.get 7 _ rfl
  have d6 : StepRowSem pub R (.statelessDecompLimb 6) 8 := hRun.get 8 _ rfl
  obtain ⟨hIn0, hR1⟩ := stepSem_statelessDeriveBlock0 h0
  obtain ⟨hIn1, hR2⟩ := stepSem_statelessDeriveBlock1 h1
  have hR1' : stepRegsAt R 1 = _ := hR1
  have hR2' : stepRegsAt R 2 = _ := hR2
  have hM1 : (stepRegsAt R 1).main = poseidon2Perm12 (R 0).stIn := by rw [hR1']; rfl
  have hM2 : (stepRegsAt R 2).main = stepXofState pub R := by
    have e : (stepRegsAt R 2).main = poseidon2Perm12 (R 1).stIn := by rw [hR2']; rfl
    rw [e, hIn1, hM1, hIn0]
    rfl
  have hRem2 : ∀ s < 6, (stepRegsAt R 2).rem.get s = ‹(fun _ => 0) s› := by
    intro s hs
    rw [hR2']
    rcases s with _ | _ | _ | _ | _ | _ | s
    · exact hz.symm
    · exact hz.symm
    · exact hz.symm
    · exact hz.symm
    · exact hz.symm
    · exact hz.symm
    · exact absurd hs (by omega)
  obtain ⟨l0, r0, f0⟩ := stepStatelessPack_row (by decide) d0 (fun _ => 0) hRem2
  have f0' : stepRegsAt R 3 = _ := f0
  rw [hM2] at l0 r0
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r0
  have m3 : (stepRegsAt R 3).main = stepXofState pub R := by rw [f0']; exact hM2
  obtain ⟨l1, r1, f1⟩ := stepStatelessPack_row (by decide) d1 _ r0
  have f1' : stepRegsAt R 4 = _ := f1
  rw [m3] at l1 r1
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r1
  have m4 : (stepRegsAt R 4).main = stepXofState pub R := by rw [f1']; exact m3
  obtain ⟨l2, r2, f2⟩ := stepStatelessPack_row (by decide) d2 _ r1
  have f2' : stepRegsAt R 5 = _ := f2
  rw [m4] at l2 r2
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r2
  have m5 : (stepRegsAt R 5).main = stepXofState pub R := by rw [f2']; exact m4
  obtain ⟨l3, r3, f3⟩ := stepStatelessPack_row (by decide) d3 _ r2
  have f3' : stepRegsAt R 6 = _ := f3
  rw [m5] at l3 r3
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r3
  have m6 : (stepRegsAt R 6).main = stepXofState pub R := by rw [f3']; exact m5
  obtain ⟨l4, r4, f4⟩ := stepStatelessPack_row (by decide) d4 _ r3
  have f4' : stepRegsAt R 7 = _ := f4
  rw [m6] at l4 r4
  simp only [Nat.reduceMul, Nat.reduceLT, ↓reduceIte] at r4
  have m7 : (stepRegsAt R 7).main = stepXofState pub R := by rw [f4']; exact m6
  obtain ⟨hD5, hR8⟩ := stepSem_statelessDecompLimb5 d5
  have hR8' : stepRegsAt R 8 = _ := hR8
  have m8 : (stepRegsAt R 8).main = stepXofState pub R := by rw [hR8']; exact m7
  obtain ⟨hD6, hR9⟩ := stepSem_statelessDecompLimb6 d6
  have hR9' : stepRegsAt R 9 = _ := hR9
  obtain ⟨hLt5, hAux5, _⟩ := (stepLimb63Decomp_allZero_iff _ 5).mp hD5
  obtain ⟨hLt6, hAux6, _⟩ := (stepLimb63Decomp_allZero_iff _ 6).mp hD6
  have hL5 : (stepOpRowInputsPerm pub (R 7)).prev (stMainSponge + 5) =
      (stepXofState pub R).b1.x1 := by
    rw [← m7]; rfl
  have hL6 : (stepOpRowInputsPerm pub (R 8)).prev (stMainSponge + 6) =
      (stepXofState pub R).b1.x2 := by
    rw [← m8]; rfl
  rw [hL5] at hLt5 hAux5
  rw [hL6] at hLt6 hAux6
  have hKp8 : (stepRegsAt R 8).kp = ‹(stepXofState pub R).b1.x1.val % 16› := by
    rw [hR8']
    exact stepLow4_eq _ _ hAux5
  have hLo8 : (stepRegsAt R 8).treeLo = ‹((stepXofState pub R).b1.x1.val / 16) % 4 ^ 14› := by
    rw [hR8']
    exact stepHi28_eq _ _ hAux5
  have hHi8 : (stepRegsAt R 8).treeHi = (stepRegsAt R 7).treeHi := by rw [hR8']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    · exact l0
    · exact l1
    · exact l2
    · exact l3
    · exact l4
    · exact hLt5
    · exact hLt6
    · exact absurd hl (by omega)
  · intro s hs
    have e9 : (stepRegsAt R 9).rem = (stepRegsAt R 7).rem := by rw [hR9', hR8']
    rw [e9, range'_32_split, stepPackFoldG_append, stepPackFoldG_append, stepPackFoldG_append,
      stepPackFoldG_append]
    exact r4 s hs
  · have e : (stepRegsAt R 9).kp = (stepRegsAt R 8).kp := by rw [hR9']
    rw [e, hKp8]
    exact congrArg Goldilocks.ofNat (by unfold stepXofLeaf; omega)
  · have e : (stepRegsAt R 9).treeLo = (stepRegsAt R 8).treeLo +ₚ
        ((stepAux R 8 0 +ₚ (stepAux R 8 1 *ₚ ‹4›)) *ₚ ‹2 ^ 28›) := by rw [hR9']
    have e2 : stepAux R 8 0 +ₚ (stepAux R 8 1 *ₚ ‹4›) =
        ‹(stepXofState pub R).b1.x2.val % 16› := stepLow4_eq _ _ hAux6
    rw [e, e2, hLo8, ← g_ofNat_mul, ← g_ofNat_add]
    exact congrArg Goldilocks.ofNat (by unfold stepXofLeaf; omega)
  · have e : (stepRegsAt R 9).treeHi = stepHi28 (stepOpRowInputsPerm pub (R 8)) := by rw [hR9']
    rw [e, stepHi28_eq _ _ hAux6]
    exact congrArg Goldilocks.ofNat (by unfold stepXofLeaf; omega)

/-! ### §3.16. FORS rows: 32 openings and the sponge of their roots -/

/-- The 17 rows of one FORS tree: the leaf hash, then per level one `ForsMerkleBlockA` and one
    `ForsMerkleBlockB` row. -/
def stepForsTreeOps (j : Nat) (odd : Bool) : List StepOp :=
  [StepOp.forsLeafHash j (j / 6)] ++
  (List.range 8).flatMap (fun lvl =>
    [StepOp.forsMerkleBlockA j lvl, StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) odd])

/-- The FORS leaf index read from the four base-4 digits of a `ForsLeafHash` row. -/
def stepForsIdxN (R : Nat → StepOpRow) (t : Nat) : Nat :=
  stepWeightedNat (fun k => stepAux R t (4 + k)) (fun k => 4 ^ k) 4

/-- The FORS opening read from the rows of a tree whose `ForsLeafHash` row is `T`. -/
def stepForsOpening (R : Nat → StepOpRow) (T : Nat) : AggForsTreeOpening :=
  ⟨stepAuxLane R T 0, (List.range 8).map (fun l => stepAuxLane R (T + 1 + 2 * l) 2)⟩

/-- The FORS node address limb of the rows equals the native node address. -/
private theorem stepNodeHashF_fors (pkSeed : Lane4) (tree kpN j l par : Nat) (L Rr : Lane4)
    (hk : kpN < 16) (hj : j < 32) (hl : l < 8) (hp : par < 256) :
    stepNodeHashF domainForsNode
        ((‹(l + 1) * 2 ^ 32 + j * 2 ^ (7 - l)› +ₚ (‹kpN› *ₚ ‹2 ^ 16›)) +ₚ ‹par›)
        ‹tree % 2 ^ 32› ‹(tree / 2 ^ 32) % 2 ^ 32› pkSeed L Rr =
      merkleAddrNodeHash domainForsNode pkSeed 0 tree (forsNodeAddr 8 kpN j) (1 + l) par L Rr := by
  have hMeta : (‹(l + 1) * 2 ^ 32 + j * 2 ^ (7 - l)› +ₚ (‹kpN› *ₚ ‹2 ^ 16›)) +ₚ ‹par› =
      ‹(0 % 65536) * 2 ^ 48 + ((1 + l) % 65536) * 2 ^ 32 +
        (forsNodeAddr 8 kpN j (1 + l) par % 2 ^ 32)› := by
    rw [← g_ofNat_mul, ← g_ofNat_add, ← g_ofNat_add]
    refine congrArg Goldilocks.ofNat ?_
    unfold forsNodeAddr
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, show 8 - (1 + l) = 7 - l by omega]
    have hX : j * 2 ^ (7 - l) ≤ 31 * 2 ^ 7 :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  unfold merkleAddrNodeHash merkleNodeHash stepNodeHashF
  rw [hMeta]

/-- What the 17 rows of FORS tree `j` starting at row `T` establish. -/
structure StepForsTreeFacts (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (kpN tree j : Nat) (odd : Bool) (T : Nat) : Prop where
  idxLt : stepForsIdxN R T < 256
  get : (stepRegsAt R T).rem.get (j / 6) =
    ‹stepForsIdxN R T› +ₚ (stepAux R T 8 *ₚ ‹256›)
  set : (stepRegsAt R (T + 17)).rem = (stepRegsAt R T).rem.set (j / 6) (stepAux R T 8)
  root : merkleWalkRoot domainForsNode pub.1.pkSeed 0 tree (forsNodeAddr 8 kpN j) 1
      (stepForsIdxN R T)
      (poseidon2Compress12FF (stepAuxLane R T 0) pub.1.pkSeed
        ⟨domainForsLeaf, ‹(kpN <<< 24) ||| ((j <<< 8) ||| stepForsIdxN R T)›,
         ‹tree % 2 ^ 32›, ‹(tree / 2 ^ 32) % 2 ^ 32›⟩)
      ((List.range 8).map (fun l => stepAuxLane R (T + 1 + 2 * l) 2)) =
    (stepPermAt R (T + 16)).b0
  kp : (stepRegsAt R (T + 17)).kp = (stepRegsAt R T).kp
  treeLo : (stepRegsAt R (T + 17)).treeLo = (stepRegsAt R T).treeLo
  treeHi : (stepRegsAt R (T + 17)).treeHi = (stepRegsAt R T).treeHi
  main : (stepRegsAt R (T + 17)).main = (stepRegsAt R T).main
  outE : odd = false → (stepRegsAt R (T + 17)).curRoot = (stepPermAt R (T + 16)).b0
  outO : odd = true → (stepRegsAt R (T + 17)).work = (stepPermAt R (T + 16)).b0 ∧
    (stepRegsAt R (T + 17)).curRoot = (stepRegsAt R T).curRoot

/-- **FORS tree rows.** The 17 rows of one tree hash the opened leaf under the tree's leaf
    address, walk its authentication path under the tree's node addresses, and consume one
    byte of the packed indices. -/
theorem stepForsTree_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {j kpN tree T : Nat} {odd : Bool}
    (hRun : StepRunAt pub R (stepForsTreeOps j odd) T)
    (hAddr : StepAddrOk (stepRegsAt R T) kpN tree) (hk : kpN < 16) (hj : j < 32) :
    StepForsTreeFacts pub R kpN tree j odd T := by
  have hLeaf : StepRowSem pub R (.forsLeafHash j (j / 6)) T := hRun.append_left.head
  have hLvRun : StepRunAt pub R ((List.range 8).flatMap (fun lvl =>
      [StepOp.forsMerkleBlockA j lvl, StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) odd]))
      (T + 1) := hRun.append_right
  have hLv := StepRunAt.flatMap_range (L := 2) (fun _ => rfl) 8 hLvRun
  have hArow : ∀ l < 8, StepRowSem pub R (.forsMerkleBlockA j l) (T + 1 + 2 * l) := by
    intro l hl
    have h := (hLv l hl).head
    rw [Nat.mul_comm l 2] at h
    exact h
  have hBrow : ∀ l < 8,
      StepRowSem pub R (.forsMerkleBlockB l (l + 1 == 8) odd) (T + 1 + 2 * l + 1) := by
    intro l hl
    have h := (hLv l hl).tail.head
    rw [Nat.mul_comm l 2] at h
    exact h
  obtain ⟨hDig, hGet, hInL, hRL⟩ := stepSem_forsLeafHash (by omega : j / 6 < 6) hLeaf
  have hRL' : stepRegsAt R (T + 1) = _ := hRL
  have hIdxEq : stepForsIdxF R T = ‹stepForsIdxN R T› := stepWeightedSum_eq_ofNat _ _ _
  have hIdxLt : stepForsIdxN R T < 256 := stepWeightedNat_lt 4 _ 4 hDig
  have hLast : StepRowSem pub R (.forsMerkleBlockB 7 true odd) (T + 16) := hBrow 7 (by decide)
  have hLastFacts : (R (T + 16)).stIn = stepMerkleBIn (stepRegsAt R (T + 16)) ∧
      (stepRegsAt R (T + 16)).cursor = Goldilocks.zero := by
    cases odd
    · obtain ⟨a, b, _⟩ := stepSem_forsMerkleBlockB_even hLast
      exact ⟨a, b⟩
    · obtain ⟨a, b, _⟩ := stepSem_forsMerkleBlockB_odd hLast
      exact ⟨a, b⟩
  have hInner : ∀ l, l < 7 →
      (R (T + 1 + 2 * l + 1)).stIn = stepMerkleBIn (stepRegsAt R (T + 1 + 2 * l + 1)) ∧
      stepRegsAt R (T + 1 + 2 * l + 2) =
        { stepRegsAt R (T + 1 + 2 * l + 1) with
          work := (stepPermAt R (T + 1 + 2 * l + 1)).b0 } := by
    intro l hl
    have h := hBrow l (by omega)
    rw [beq_false_of_ne (by omega : l + 1 ≠ 8)] at h
    exact stepSem_forsMerkleBlockB_inner h
  have kp1 : (stepRegsAt R (T + 1)).kp = (stepRegsAt R T).kp := by rw [hRL']
  have lo1 : (stepRegsAt R (T + 1)).treeLo = (stepRegsAt R T).treeLo := by rw [hRL']
  have hi1 : (stepRegsAt R (T + 1)).treeHi = (stepRegsAt R T).treeHi := by rw [hRL']
  have main1 : (stepRegsAt R (T + 1)).main = (stepRegsAt R T).main := by rw [hRL']
  have cur1 : (stepRegsAt R (T + 1)).curRoot = (stepRegsAt R T).curRoot := by rw [hRL']
  have rem1 : (stepRegsAt R (T + 1)).rem = (stepRegsAt R T).rem.set (j / 6) (stepAux R T 8) := by
    rw [hRL']
  have hFr : ∀ l, l ≤ 7 →
      StepFrameSWC (stepRegsAt R (T + 1 + 2 * l)) (stepRegsAt R (T + 1)) := by
    intro l
    induction l with
    | zero => intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    | succ l ih =>
      intro hl
      have iF := ih (by omega)
      have hA := (stepMerkleARow_fors (hArow l (by omega))).next
      have hB := (hInner l (by omega)).2
      have e : T + 1 + 2 * (l + 1) = T + 1 + 2 * l + 2 := by omega
      rw [e, hB, hA]
      exact ⟨iF.curRoot, iF.kp, iF.treeLo, iF.treeHi, iF.rem, iF.main⟩
  have hKpRow : ∀ l < 8, (stepRegsAt R (T + 1 + 2 * l)).kp = ‹kpN› :=
    fun l hl => ((hFr l (by omega)).kp.trans kp1).trans hAddr.kp
  have hA' : ∀ l < 8, StepMerkleARow pub R (T + 1 + 2 * l) domainForsNode
      (‹(l + 1) * 2 ^ 32 + j * 2 ^ (7 - l)› +ₚ (‹kpN› *ₚ ‹2 ^ 16›)) := by
    intro l hl
    have h := stepMerkleARow_fors (hArow l hl)
    rw [hKpRow l hl] at h
    exact h
  obtain ⟨_, hWalk, hFr16⟩ := stepMerkle_sem (layerV := 0) (treeV := tree)
    (addr := forsNodeAddr 8 kpN j) (idx0 := stepForsIdxN R T) (t1 := T + 1) (h := 8) hA'
    (fun l hl => by
      by_cases h7 : l < 7
      · exact (hInner l h7).1
      · have e : l = 7 := by omega
        subst e
        exact hLastFacts.1)
    (fun l hl => (hInner l (by omega)).2)
    hLastFacts.2
    (by rw [hRL']; exact hIdxEq)
    (by omega) (by decide) (by decide)
    (fun l hl _ L Rr => by
      rw [lo1, hi1, hAddr.lo, hAddr.hi]
      exact stepNodeHashF_fors pub.1.pkSeed tree kpN j l (stepForsIdxN R T / 2 ^ (l + 1)) L Rr
        hk hj hl (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hIdxLt))
  have hFr16' : StepFrameSWC (stepRegsAt R (T + 16)) (stepRegsAt R (T + 1)) := hFr16
  have hLeafWork : (stepRegsAt R (T + 1)).work =
      poseidon2Compress12FF (stepAuxLane R T 0) pub.1.pkSeed
        ⟨domainForsLeaf, ‹(kpN <<< 24) ||| ((j <<< 8) ||| stepForsIdxN R T)›,
         ‹tree % 2 ^ 32›, ‹(tree / 2 ^ 32) % 2 ^ 32›⟩ := by
    have hTw : (‹kpN› *ₚ ‹2 ^ 24›) +ₚ (‹j * 2 ^ 8› +ₚ ‹stepForsIdxN R T›) =
        ‹(kpN <<< 24) ||| ((j <<< 8) ||| stepForsIdxN R T)› := by
      have h8 : stepForsIdxN R T < 2 ^ 8 := hIdxLt
      have h1 : j <<< 8 ||| stepForsIdxN R T = j <<< 8 + stepForsIdxN R T :=
        (Nat.shiftLeft_add_eq_or_of_lt h8 j).symm
      have hb : j <<< 8 + stepForsIdxN R T < 2 ^ 24 := by
        rw [Nat.shiftLeft_eq]
        omega
      have h2 : kpN <<< 24 ||| (j <<< 8 + stepForsIdxN R T) =
          kpN <<< 24 + (j <<< 8 + stepForsIdxN R T) :=
        (Nat.shiftLeft_add_eq_or_of_lt hb kpN).symm
      rw [h1, h2, Nat.shiftLeft_eq, Nat.shiftLeft_eq, ← g_ofNat_mul, ← g_ofNat_add,
        ← g_ofNat_add]
    rw [hRL']
    show lane4Add (stepPermAt R T).b0 (stepAuxLane R T 0) = _
    unfold poseidon2Compress12FF stepPermAt
    rw [hInL, hAddr.kp, hAddr.lo, hAddr.hi, hIdxEq, hTw]
  rw [hLeafWork] at hWalk
  rw [hIdxEq] at hGet
  have hOut : (stepRegsAt R (T + 17)).rem = (stepRegsAt R (T + 16)).rem ∧
      (stepRegsAt R (T + 17)).kp = (stepRegsAt R (T + 16)).kp ∧
      (stepRegsAt R (T + 17)).treeLo = (stepRegsAt R (T + 16)).treeLo ∧
      (stepRegsAt R (T + 17)).treeHi = (stepRegsAt R (T + 16)).treeHi ∧
      (stepRegsAt R (T + 17)).main = (stepRegsAt R (T + 16)).main ∧
      (odd = false → (stepRegsAt R (T + 17)).curRoot = (stepPermAt R (T + 16)).b0) ∧
      (odd = true → (stepRegsAt R (T + 17)).work = (stepPermAt R (T + 16)).b0 ∧
        (stepRegsAt R (T + 17)).curRoot = (stepRegsAt R (T + 16)).curRoot) := by
    cases odd
    · obtain ⟨_, _, hN⟩ := stepSem_forsMerkleBlockB_even hLast
      have hN' : stepRegsAt R (T + 17) = _ := hN
      rw [hN']
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun h => Bool.noConfusion h⟩
    · obtain ⟨_, _, hN⟩ := stepSem_forsMerkleBlockB_odd hLast
      have hN' : stepRegsAt R (T + 17) = _ := hN
      rw [hN']
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun h => Bool.noConfusion h, fun _ => ⟨rfl, rfl⟩⟩
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := hOut
  exact
    { idxLt := hIdxLt
      get := hGet
      set := o1.trans (hFr16'.rem.trans rem1)
      root := hWalk
      kp := o2.trans (hFr16'.kp.trans kp1)
      treeLo := o3.trans (hFr16'.treeLo.trans lo1)
      treeHi := o4.trans (hFr16'.treeHi.trans hi1)
      main := o5.trans (hFr16'.main.trans main1)
      outE := o6
      outO := fun h => ⟨(o7 h).1, (o7 h).2.trans (hFr16'.curRoot.trans cur1)⟩ }

/-- One FORS pair: two trees and the absorption of their roots. -/
def stepForsPairOps (pair : Nat) : List StepOp :=
  (List.range 2).flatMap (fun sub =>
    [StepOp.forsLeafHash (2 * pair + sub) ((2 * pair + sub) / 6)] ++
    (List.range 8).flatMap (fun lvl =>
      [StepOp.forsMerkleBlockA (2 * pair + sub) lvl,
       StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) (sub == 1)])) ++
  [StepOp.forsRootsPairAbsorb pair]

/-- What the 35 rows of FORS pair `pair` starting at row `T` establish. -/
structure StepForsPairFacts (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (kpN tree pair T : Nat) : Prop where
  E : StepForsTreeFacts pub R kpN tree (2 * pair) false T
  O : StepForsTreeFacts pub R kpN tree (2 * pair + 1) true (T + 17)
  rem : (stepRegsAt R (T + 35)).rem = (stepRegsAt R (T + 34)).rem
  zero : (pair + 1 == 16) = true → ∀ s < 6, (stepRegsAt R (T + 34)).rem.get s = Goldilocks.zero
  main : (stepRegsAt R (T + 35)).main =
    poseidon2Perm12
      ⟨lane4Add (stepRegsAt R T).main.b0 (stepPermAt R (T + 16)).b0,
       lane4Add (stepRegsAt R T).main.b1 (stepPermAt R (T + 33)).b0,
       (stepRegsAt R T).main.b2⟩
  kp : (stepRegsAt R (T + 35)).kp = (stepRegsAt R T).kp
  treeLo : (stepRegsAt R (T + 35)).treeLo = (stepRegsAt R T).treeLo
  treeHi : (stepRegsAt R (T + 35)).treeHi = (stepRegsAt R T).treeHi

theorem stepForsPair_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {pair kpN tree T : Nat}
    (hRun : StepRunAt pub R (stepForsPairOps pair) T)
    (hAddr : StepAddrOk (stepRegsAt R T) kpN tree) (hk : kpN < 16) (hp : pair < 16) :
    StepForsPairFacts pub R kpN tree pair T := by
  have hTrees : StepRunAt pub R ((List.range 2).flatMap (fun sub =>
      [StepOp.forsLeafHash (2 * pair + sub) ((2 * pair + sub) / 6)] ++
      (List.range 8).flatMap (fun lvl =>
        [StepOp.forsMerkleBlockA (2 * pair + sub) lvl,
         StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) (sub == 1)]))) T := hRun.append_left
  have hTree := StepRunAt.flatMap_range (L := 17) (fun _ => rfl) 2 hTrees
  have hE : StepRunAt pub R (stepForsTreeOps (2 * pair) false) T := hTree 0 (by decide)
  have hO : StepRunAt pub R (stepForsTreeOps (2 * pair + 1) true) (T + 17) :=
    hTree 1 (by decide)
  have hAbs : StepRowSem pub R (.forsRootsPairAbsorb pair) (T + 34) := hRun.get 34 _ rfl
  have E := stepForsTree_sem hE hAddr hk (by omega)
  have hAddr17 : StepAddrOk (stepRegsAt R (T + 17)) kpN tree :=
    ⟨E.kp.trans hAddr.kp, E.treeLo.trans hAddr.lo, E.treeHi.trans hAddr.hi⟩
  have O := stepForsTree_sem hO hAddr17 hk (by omega)
  obtain ⟨hZ, hInA, hRA⟩ := stepSem_forsRootsPairAbsorb hAbs
  have hRA' : stepRegsAt R (T + 35) = _ := hRA
  have m34 : (stepRegsAt R (T + 34)).main = (stepRegsAt R T).main := O.main.trans E.main
  have c34 : (stepRegsAt R (T + 34)).curRoot = (stepPermAt R (T + 16)).b0 :=
    (O.outO rfl).2.trans (E.outE rfl)
  have w34 : (stepRegsAt R (T + 34)).work = (stepPermAt R (T + 33)).b0 := (O.outO rfl).1
  have k34 : (stepRegsAt R (T + 34)).kp = (stepRegsAt R T).kp := O.kp.trans E.kp
  have lo34 : (stepRegsAt R (T + 34)).treeLo = (stepRegsAt R T).treeLo :=
    O.treeLo.trans E.treeLo
  have hi34 : (stepRegsAt R (T + 34)).treeHi = (stepRegsAt R T).treeHi :=
    O.treeHi.trans E.treeHi
  refine
    { E := E, O := O, rem := by rw [hRA'], zero := hZ, main := ?_, kp := ?_, treeLo := ?_,
      treeHi := ?_ }
  · rw [hRA']
    show poseidon2Perm12 (R (T + 34)).stIn = _
    rw [hInA, m34, c34, w34]
  · rw [hRA']; exact k34
  · rw [hRA']; exact lo34
  · rw [hRA']; exact hi34

/-- Row of the `ForsLeafHash` of tree `j` when the `ForsRootsSpongeInit` row is `t0`. -/
def stepForsRow (t0 j : Nat) : Nat := t0 + 1 + 35 * (j / 2) + 17 * (j % 2)

/-- Root of FORS tree `j` as computed by its rows. -/
def stepForsRoot (R : Nat → StepOpRow) (t0 j : Nat) : Lane4 :=
  (stepPermAt R (stepForsRow t0 j + 16)).b0

/-- A FORS opening whose authentication path walks to `rt` is accepted with root `rt`. -/
theorem verifySingleForsOpening_intro (geom : AggSigGeometry) (pkSeed : Digest4)
    (leaf j idx : Nat) (secret : Digest4) (path : List Digest4) (rt : Digest4)
    (hIdx : idx < 2 ^ geom.forsHeight) (hLen : path.length = geom.forsHeight)
    (hWalk : merkleWalkRoot domainForsNode pkSeed 0 (forsHyperTreeIdx geom leaf)
      (forsTreeNodeAddr geom leaf j) 1 idx (forsLeafHash geom pkSeed secret leaf j idx) path =
      rt) :
    verifySingleForsOpening geom pkSeed leaf j idx ⟨secret, path⟩ = some rt := by
  unfold verifySingleForsOpening
  simp only [hIdx, hLen, decide_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  exact congrArg some hWalk

/-- **FORS rows.** The 562 rows `ForsRootsSpongeInit .. ForsRootsFinalSqueeze` verify 32 FORS
    openings read from the auxiliary columns, unpack exactly the packed indices, and leave in
    `ST_CUR_ROOT` the sponge of the 32 recovered roots. -/
theorem stepFors_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow} {t0 leaf : Nat}
    (hInit : StepRowSem pub R .forsRootsSpongeInit t0)
    (hPairs : StepRunAt pub R ((List.range 16).flatMap stepForsPairOps) (t0 + 1))
    (hSq : StepRowSem pub R .forsRootsFinalSqueeze (t0 + 561))
    (hAddr : StepAddrOk (stepRegsAt R t0) (leaf % 16) (leaf / 16)) :
    (∀ j < 32, stepForsIdxN R (stepForsRow t0 j) < 256) ∧
    (∀ s a len : Nat, (∀ c < 32, c / 6 = s ↔ a ≤ c ∧ c < a + len) → s < 6 → a + len ≤ 32 →
      256 ^ len < goldilocksPrime →
      ((stepRegsAt R t0).rem.get s).val =
        evalBaseDigits 256
          ((List.range' a len).map (fun c => stepForsIdxN R (stepForsRow t0 c)))) ∧
    (∀ j < 32, verifySingleForsOpening corduroyPoseidon2Geom pub.1.pkSeed leaf j
        (stepForsIdxN R (stepForsRow t0 j)) (stepForsOpening R (stepForsRow t0 j)) =
      some (stepForsRoot R t0 j)) ∧
    (stepRegsAt R (t0 + 562)).curRoot =
      compressForsRootsSponge corduroyPoseidon2Geom pub.1.pkSeed leaf
        ((List.range 32).map (stepForsRoot R t0)) ∧
    StepAddrOk (stepRegsAt R (t0 + 562)) (leaf % 16) (leaf / 16) := by
  have hk : leaf % 16 < 16 := Nat.mod_lt _ (by decide)
  have hPair : ∀ p < 16, StepRunAt pub R (stepForsPairOps p) (t0 + 1 + p * 35) :=
    StepRunAt.flatMap_range (L := 35) (fun _ => rfl) 16 hPairs
  obtain ⟨hInInit, hR1⟩ := stepSem_forsRootsSpongeInit hInit
  have hFrame : ∀ p, p ≤ 16 →
      (stepRegsAt R (t0 + 1 + p * 35)).kp = (stepRegsAt R t0).kp ∧
      (stepRegsAt R (t0 + 1 + p * 35)).treeLo = (stepRegsAt R t0).treeLo ∧
      (stepRegsAt R (t0 + 1 + p * 35)).treeHi = (stepRegsAt R t0).treeHi := by
    intro p
    induction p with
    | zero =>
      intro _
      have h0 : stepRegsAt R (t0 + 1 + 0 * 35) = _ := hR1
      rw [h0]
      exact ⟨rfl, rfl, rfl⟩
    | succ p ih =>
      intro hp
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
      have hA : StepAddrOk (stepRegsAt R (t0 + 1 + p * 35)) (leaf % 16) (leaf / 16) :=
        ⟨i1.trans hAddr.kp, i2.trans hAddr.lo, i3.trans hAddr.hi⟩
      have F := stepForsPair_sem (hPair p (by omega)) hA hk (by omega)
      have e : t0 + 1 + (p + 1) * 35 = t0 + 1 + p * 35 + 35 := by omega
      rw [e]
      exact ⟨F.kp.trans i1, F.treeLo.trans i2, F.treeHi.trans i3⟩
  have hF : ∀ p, p < 16 →
      StepForsPairFacts pub R (leaf % 16) (leaf / 16) p (t0 + 1 + p * 35) := by
    intro p hp
    obtain ⟨i1, i2, i3⟩ := hFrame p (by omega)
    exact stepForsPair_sem (hPair p hp)
      ⟨i1.trans hAddr.kp, i2.trans hAddr.lo, i3.trans hAddr.hi⟩ hk hp
  have rowE : ∀ p, stepForsRow t0 (2 * p) = t0 + 1 + p * 35 := by
    intro p; unfold stepForsRow; omega
  have rowO : ∀ p, stepForsRow t0 (2 * p + 1) = t0 + 1 + p * 35 + 17 := by
    intro p; unfold stepForsRow; omega
  have rowN : ∀ p, stepForsRow t0 (2 * p + 1 + 1) = t0 + 1 + p * 35 + 35 := by
    intro p; unfold stepForsRow; omega
  have rootE : ∀ p, stepForsRoot R t0 (2 * p) = (stepPermAt R (t0 + 1 + p * 35 + 16)).b0 := by
    intro p; unfold stepForsRoot; rw [rowE]
  have rootO : ∀ p, stepForsRoot R t0 (2 * p + 1) =
      (stepPermAt R (t0 + 1 + p * 35 + 33)).b0 := by
    intro p; unfold stepForsRoot; rw [rowO]
  have hSplit : ∀ c, c < 32 → ∃ p, p < 16 ∧ (c = 2 * p ∨ c = 2 * p + 1) :=
    fun c hc => ⟨c / 2, by omega, by omega⟩
  have hd : ∀ c < 32, stepForsIdxN R (stepForsRow t0 c) < 256 := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE]; exact (hF p hp).E.idxLt
    · rw [rowO]; exact (hF p hp).O.idxLt
  have hget : ∀ c < 32, ((stepRegsAt R (stepForsRow t0 c)).rem).get (c / 6) =
      ‹stepForsIdxN R (stepForsRow t0 c)› +ₚ (stepAux R (stepForsRow t0 c) 8 *ₚ ‹256›) := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE]; exact (hF p hp).E.get
    · rw [rowO]; exact (hF p hp).O.get
  have hset : ∀ c < 32, (stepRegsAt R (stepForsRow t0 (c + 1))).rem =
      ((stepRegsAt R (stepForsRow t0 c)).rem).set (c / 6)
        (stepAux R (stepForsRow t0 c) 8) := by
    intro c hc
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit c hc
    · rw [rowE, rowO]; exact (hF p hp).E.set
    · rw [rowO, rowN]; exact (hF p hp).rem.trans (hF p hp).O.set
  have hEnd : ∀ s < 6, ((stepRegsAt R (stepForsRow t0 32)).rem).get s = Goldilocks.zero := by
    intro s hs
    have e : stepForsRow t0 32 = t0 + 1 + 15 * 35 + 35 := by unfold stepForsRow; omega
    rw [e, (hF 15 (by decide)).rem]
    exact (hF 15 (by decide)).zero rfl s hs
  have hG0 : (stepRegsAt R (stepForsRow t0 0)).rem = (stepRegsAt R t0).rem := by
    have e : stepForsRow t0 0 = t0 + 1 := by unfold stepForsRow; omega
    rw [e, hR1]
  have hMain : ∀ p, p ≤ 16 → (stepRegsAt R (t0 + 1 + p * 35)).main =
      absorbDigest4Pairs (stepPermAt R t0) ((List.range (2 * p)).map (stepForsRoot R t0)) := by
    intro p
    induction p with
    | zero =>
      intro _
      have h0 : stepRegsAt R (t0 + 1 + 0 * 35) = _ := hR1
      rw [h0]
      rfl
    | succ p ih =>
      intro hp
      have F := hF p (by omega)
      have e : t0 + 1 + (p + 1) * 35 = t0 + 1 + p * 35 + 35 := by omega
      have e2 : 2 * (p + 1) = 2 * p + 1 + 1 := by omega
      rw [e, F.main, ih (by omega), e2, List.range_succ, List.range_succ, List.append_assoc,
        List.map_append]
      unfold absorbDigest4Pairs
      have hEven : ((List.range (2 * p)).map (stepForsRoot R t0)).length % 2 = 0 := by
        rw [List.length_map, List.length_range]
        omega
      have hApp := absorbPairsPoly_append_pair
        (fun (s : Poseidon2State12) (e0 : Lane4) =>
          poseidon2Perm12 ⟨lane4Add s.b0 e0, s.b1, s.b2⟩)
        (fun (s : Poseidon2State12) (e0 e1 : Lane4) =>
          poseidon2Perm12 ⟨lane4Add s.b0 e0, lane4Add s.b1 e1, s.b2⟩)
        (stepPermAt R (t0 + 1 + p * 35 + 16)).b0 (stepPermAt R (t0 + 1 + p * 35 + 33)).b0
        _ (stepPermAt R t0) hEven
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
      rw [rootE, rootO]
      exact hApp.symm
  obtain ⟨hInSq, hR562⟩ := stepSem_forsRootsFinalSqueeze hSq
  have hR562' : stepRegsAt R (t0 + 562) = _ := hR562
  obtain ⟨f1, f2, f3⟩ := hFrame 16 (Nat.le_refl _)
  have e16 : t0 + 1 + 16 * 35 = t0 + 561 := by omega
  rw [e16] at f1 f2 f3
  have hM16 := hMain 16 (Nat.le_refl _)
  rw [e16] at hM16
  refine ⟨hd, ?_, ?_, ?_, ?_⟩
  · intro s a len hRange hs haN hLen
    have h := stepRemSlot_digits
      (fun c => (stepRegsAt R (stepForsRow t0 c)).rem) 256 (by decide)
      (fun c => stepForsIdxN R (stepForsRow t0 c))
      (fun c => stepAux R (stepForsRow t0 c) 8) (fun c => c / 6) 32
      hd hget hset (fun c hc => by show c / 6 < 6; omega) s a len hRange haN (hEnd s hs) hLen
    rw [← hG0]
    exact h
  · intro j hj
    obtain ⟨p, hp, rfl | rfl⟩ := hSplit j hj
    · rw [rootE, rowE]
      exact verifySingleForsOpening_intro corduroyPoseidon2Geom _ leaf (2 * p) _ _ _ _
        (hF p hp).E.idxLt (by rw [List.length_map, List.length_range]; rfl) (hF p hp).E.root
    · rw [rootO, rowO]
      exact verifySingleForsOpening_intro corduroyPoseidon2Geom _ leaf (2 * p + 1) _ _ _ _
        (hF p hp).O.idxLt (by rw [List.length_map, List.length_range]; rfl) (hF p hp).O.root
  · have hInit' : (R t0).stIn =
        ⟨pub.1.pkSeed,
         ⟨‹leaf % 16›, ‹(leaf / 16) % 2 ^ 32›, ‹(leaf / 16 / 2 ^ 32) % 2 ^ 32›, ‹32›⟩,
         ⟨domainForsRoots, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩ := by
      rw [hInInit, hAddr.kp, hAddr.lo, hAddr.hi]
    rw [hR562']
    show (stepPermAt R (t0 + 561)).b0 = _
    unfold stepPermAt
    rw [hInSq]
    unfold stepSqueezeIn
    rw [hM16]
    unfold stepPermAt compressForsRootsSponge
    rw [hInit']
    rfl
  · rw [hR562']
    exact ⟨f1.trans hAddr.kp, f2.trans hAddr.lo, f3.trans hAddr.hi⟩

/-! ### §3.17. Hypertree layers of the stateless profile -/

/-- The 465 rows of one hypertree layer of the stateless profile. -/
def stepCordLayerOps (layer : Nat) (isTop : Bool) : List StepOp :=
  [StepOp.detTreeHmsgBlock0 layer, StepOp.detTreeHmsgBlock1 layer] ++
    (List.range 5).map StepOp.hmsgDecompLimb ++ pushLayerWotsAndMerkle layer 4 isTop

/-- The WOTS+C counter read from the 32 bits of a `DetTreeHmsgBlock1` row; `tL` is the row of
    the layer's `DetTreeHmsgBlock0`. -/
def stepCordCtr (R : Nat → StepOpRow) (tL : Nat) : Nat :=
  stepWeightedNat (stepAux R (tL + 1)) (fun i => 2 ^ i) 32

/-- The layer signature read from the rows of a layer starting at row `tL`. -/
def stepCordLayerSig (R : Nat → StepOpRow) (tL : Nat) : WotsLayerSig :=
  ⟨stepCordCtr R tL, stepLayerChains R (tL + 7), stepLayerPath R (tL + 457) 4⟩

/-- **Stateless layer rows.** The 465 rows of a layer hash the child root in `ST_CUR_ROOT`
    under the deterministic tree `H_msg`, verify one WOTS+C layer against it, and either pin
    the walked root to the public key (top layer) or move it to `ST_CUR_ROOT` and shift the
    tree index by the subtree height (inner layers). -/
theorem stepCordLayer_sem {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {layer tL kpN tree : Nat} {isTop : Bool}
    (hRun : StepRunAt pub R (stepCordLayerOps layer isTop) tL)
    (hAddr : StepAddrOk (stepRegsAt R tL) kpN tree) (hl : layer < 16) (hk : kpN < 16) :
    verifyWotsLayer corduroyPoseidon2Geom pub.1 layer tree kpN
        (computeHmsgDetTree pub.1 layer tree kpN (stepCordLayerSig R tL).tswCtr
          (stepRegsAt R tL).curRoot)
        (stepCordLayerSig R tL) =
      some (stepPermAt R (tL + 464)).b0 ∧
    (isTop = true → (stepPermAt R (tL + 464)).b0 = pub.1.pkRoot) ∧
    (isTop = false → tree < 2 ^ 64 →
      StepAddrOk (stepRegsAt R (tL + 465)) (tree % 16) (tree / 16) ∧
      (stepRegsAt R (tL + 465)).curRoot = (stepPermAt R (tL + 464)).b0) := by
  have b0 : StepRowSem pub R (.detTreeHmsgBlock0 layer) tL := hRun.get 0 _ rfl
  have b1 : StepRowSem pub R (.detTreeHmsgBlock1 layer) (tL + 1) := hRun.get 1 _ rfl
  have hDec : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) (tL + 2) :=
    hRun.append_left.append_right
  have hLayer : StepRunAt pub R (pushLayerWotsAndMerkle layer 4 isTop) (tL + 2 + 5) :=
    hRun.append_right
  have hLast : StepRowSem pub R (.xmssMerkleBlockB true isTop) (tL + 464) :=
    hRun.get 464 _ rfl
  obtain ⟨hIn0, hR1⟩ := stepSem_detTreeHmsgBlock0 b0
  obtain ⟨hBits, hIn1, hR2⟩ := stepSem_detTreeHmsgBlock1 b1
  have hR1' : stepRegsAt R (tL + 1) = _ := hR1
  have hR2' : stepRegsAt R (tL + 2) = _ := hR2
  have hCtr : stepCordCtr R tL < 2 ^ 32 := stepWeightedNat_bits_lt (stepAux R (tL + 1)) 32 hBits
  have hRem0 : ∀ s < 6, (stepRegsAt R (tL + 2)).rem.get s = Goldilocks.zero := by
    intro s hs
    rw [hR2']
    rcases s with _ | _ | _ | _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd hs (by omega)
  have hAcc0 : (stepRegsAt R (tL + 2)).acc = Goldilocks.zero := by rw [hR2']
  have hAddr2 : StepAddrOk (stepRegsAt R (tL + 2)) kpN tree := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hR2', hR1']; exact hAddr.kp
    · rw [hR2', hR1']; exact hAddr.lo
    · rw [hR2', hR1']; exact hAddr.hi
  have hHm : stepHmsgOf (stepRegsAt R (tL + 2)).main =
      computeHmsgDetTree pub.1 layer tree kpN (stepCordCtr R tL) (stepRegsAt R tL).curRoot := by
    have hM1 : (stepRegsAt R (tL + 1)).main = poseidon2Perm12 (R tL).stIn := by rw [hR1']; rfl
    have hM2 : (stepRegsAt R (tL + 2)).main = poseidon2Perm12 (R (tL + 1)).stIn := by
      rw [hR2']; rfl
    have hC1 : (stepRegsAt R (tL + 1)).curRoot = (stepRegsAt R tL).curRoot := by rw [hR1']
    have hLK : (‹layer * 2 ^ 32› : Goldilocks) +ₚ ‹kpN› =
        ‹(layer % 2 ^ 32) * 2 ^ 32 + kpN % 2 ^ 32› := by
      rw [← g_ofNat_add, Nat.mod_eq_of_lt (by omega : layer < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : kpN < 2 ^ 32)]
    have hCt : stepWeightedSum (stepAux R (tL + 1)) (fun i => 2 ^ i) 32 =
        ‹stepCordCtr R tL % 2 ^ 32› := by
      rw [stepWeightedSum_eq_ofNat, Nat.mod_eq_of_lt hCtr]
      rfl
    rw [hM2, hIn1, hM1, hC1, hIn0, hAddr.kp, hAddr.lo, hAddr.hi, hLK, hCt]
    rfl
  have hLastFacts : (R (tL + 464)).stIn = stepMerkleBIn (stepRegsAt R (tL + 464)) ∧
      (stepRegsAt R (tL + 464)).cursor = Goldilocks.zero := by
    cases isTop
    · obtain ⟨a, b, _⟩ := stepSem_xmssMerkleBlockB_link hLast
      exact ⟨a, b⟩
    · obtain ⟨a, b, _⟩ := stepSem_xmssMerkleBlockB_top hLast
      exact ⟨a, b⟩
  obtain ⟨_, hV, _, hAddr464⟩ := stepLayer_verify (geom := corduroyPoseidon2Geom)
    (layer := layer) (h := 4) (tD := tL + 2) (ctr := stepCordCtr R tL) hDec hLayer hRem0 hAcc0
    hAddr2 hLastFacts.1 hLastFacts.2 (by omega) (by omega) (by decide) (by decide) rfl rfl rfl
  have hAddr464' : StepAddrOk (stepRegsAt R (tL + 464)) kpN tree := hAddr464
  rw [hHm] at hV
  refine ⟨hV, ?_, ?_⟩
  · intro hT
    subst hT
    exact (stepSem_xmssMerkleBlockB_top hLast).2.2
  · intro hT hTree
    subst hT
    obtain ⟨_, _, hB4, hQa, hQ2, hQb, hLo, hHi, hRn⟩ := stepSem_xmssMerkleBlockB_link hLast
    have hRn' : stepRegsAt R (tL + 465) = _ := hRn
    have nb : stepWeightedNat (stepAux R (tL + 464)) (fun i => 2 ^ i) 4 < 2 ^ 4 :=
      stepWeightedNat_bits_lt _ 4 hB4
    have nA : stepWeightedNat (fun i => stepAux R (tL + 464) (4 + i)) (fun i => 4 ^ i) 14 <
        4 ^ 14 := stepWeightedNat_lt 4 _ 14 hQa
    have n2 : stepWeightedNat (fun i => stepAux R (tL + 464) (18 + i)) (fun i => 4 ^ i) 2 <
        4 ^ 2 := stepWeightedNat_lt 4 _ 2 hQ2
    have nB : stepWeightedNat (fun i => stepAux R (tL + 464) (20 + i)) (fun i => 4 ^ i) 14 <
        4 ^ 14 := stepWeightedNat_lt 4 _ 14 hQb
    rw [stepWeightedSum_eq_ofNat, stepWeightedSum_eq_ofNat, ← g_ofNat_mul, ← g_ofNat_add,
      hAddr464'.lo] at hLo
    rw [stepWeightedSum_eq_ofNat, stepWeightedSum_eq_ofNat, ← g_ofNat_mul, ← g_ofNat_add,
      hAddr464'.hi] at hHi
    have eLo := g_ofNat_inj (by rw [goldilocksPrime_eq]; omega)
      (by rw [goldilocksPrime_eq]; omega) hLo
    have eHi := g_ofNat_inj (by rw [goldilocksPrime_eq]; omega)
      (by rw [goldilocksPrime_eq]; omega) hHi
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hRn']
      show stepWeightedSum (stepAux R (tL + 464)) (fun i => 2 ^ i) 4 = _
      rw [stepWeightedSum_eq_ofNat]
      exact congrArg Goldilocks.ofNat (by omega)
    · rw [hRn']
      show stepWeightedSum (fun i => stepAux R (tL + 464) (4 + i)) (fun i => 4 ^ i) 14 +ₚ
        (stepWeightedSum (fun i => stepAux R (tL + 464) (18 + i)) (fun i => 4 ^ i) 2 *ₚ
          ‹2 ^ 28›) = _
      rw [stepWeightedSum_eq_ofNat, stepWeightedSum_eq_ofNat, ← g_ofNat_mul, ← g_ofNat_add]
      exact congrArg Goldilocks.ofNat (by omega)
    · rw [hRn']
      show stepWeightedSum (fun i => stepAux R (tL + 464) (20 + i)) (fun i => 4 ^ i) 14 = _
      rw [stepWeightedSum_eq_ofNat]
      exact congrArg Goldilocks.ofNat (by omega)
    · rw [hRn']

/-! ### §3.18. Active `CorduroyPoseidon2` slot: an accepted table yields a native signature -/

private theorem verifyForsPoly_map {OP D : Type} (step : Nat → Nat → OP → Option D)
    (idx : Nat → Nat) (op : Nat → OP) (rt : Nat → D) :
    ∀ (n t0 : Nat), (∀ i, t0 ≤ i → i < t0 + n → step i (idx i) (op i) = some (rt i)) →
      verifyForsPoly step ((List.range' t0 n).map idx) ((List.range' t0 n).map op) t0 =
        some ((List.range' t0 n).map rt)
  | 0, _, _ => rfl
  | n + 1, t0, h => by
    have e : List.range' t0 (n + 1) = t0 :: List.range' (t0 + 1) n := rfl
    have ih := verifyForsPoly_map step idx op rt n (t0 + 1)
      (fun i h1 h2 => h i (by omega) (by omega))
    rw [e, List.map_cons, List.map_cons, List.map_cons]
    simp only [verifyForsPoly, h t0 (Nat.le_refl _) (by omega), ih]

/-- Upper layers verify one after another when each layer verifies against the root of the
    layer below and the remaining tree index is shifted by the subtree height. -/
private theorem verifyUpperLayers_chain (geom : AggSigGeometry) (pk : AggValidatorPk)
    (sigL : Nat → WotsLayerSig) (cur : Nat → Digest4) (rem : Nat → Nat) :
    ∀ (n l0 : Nat),
      (∀ l, l0 ≤ l → l < l0 + n →
        verifyWotsLayer geom pk l (rem l / 2 ^ geom.subtreeHeight)
            (rem l % 2 ^ geom.subtreeHeight)
            (computeHmsgDetTree pk l (rem l / 2 ^ geom.subtreeHeight)
              (rem l % 2 ^ geom.subtreeHeight) (sigL l).tswCtr (cur l)) (sigL l) =
          some (cur (l + 1)) ∧
        rem (l + 1) = rem l / 2 ^ geom.subtreeHeight) →
      verifyUpperLayers geom pk l0 (rem l0) (cur l0) ((List.range' l0 n).map sigL) =
        some (cur (l0 + n))
  | 0, _, _ => rfl
  | n + 1, l0, h => by
    have e : List.range' l0 (n + 1) = l0 :: List.range' (l0 + 1) n := rfl
    have hs := h l0 (Nat.le_refl _) (by omega)
    have ih := verifyUpperLayers_chain geom pk sigL cur rem n (l0 + 1)
      (fun l h1 h2 => h l (by omega) (by omega))
    unfold verifyUpperLayers at ih ⊢
    rw [e, List.map_cons]
    simp only [verifyUpperPoly, hs.1]
    rw [← hs.2, show l0 + (n + 1) = l0 + 1 + n by omega]
    exact ih

/-- A stateless signature is accepted once the XOF derive, the FORS openings, the bottom
    layer and the upper layers each verify. -/
theorem verifyAggNativeSig_stateless_intro (geom : AggSigGeometry) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (fors : List AggForsTreeOpening)
    (lsig0 : WotsLayerSig) (upper : List WotsLayerSig)
    (leaf : Nat) (idxs : List Nat) (forsPk root0 : Digest4)
    (hWf : geom.wellFormed = true) (hPk : pk.profile = geom.profile)
    (hNL : (lsig0 :: upper).length = geom.numLayers) (hF : (geom.forsTrees == 0) = false)
    (hXof : deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) =
      some (leaf, idxs))
    (hFors : verifyAndRecoverForsPk geom pk.pkSeed leaf idxs fors = some forsPk)
    (hL0 : verifyWotsLayer geom pk 0 (leaf / 2 ^ geom.subtreeHeight)
        (leaf % 2 ^ geom.subtreeHeight)
        (computeHmsgDetTree pk 0 (leaf / 2 ^ geom.subtreeHeight)
          (leaf % 2 ^ geom.subtreeHeight) lsig0.tswCtr forsPk) lsig0 = some root0)
    (hUp : verifyUpperLayers geom pk 1 (leaf / 2 ^ geom.subtreeHeight) root0 upper =
      some pk.pkRoot) :
    verifyAggNativeSig geom pk msg ⟨geom.profile, rRand, 0, fors, lsig0 :: upper⟩ = true := by
  have hCond : (!geom.wellFormed || pk.profile != geom.profile ||
      geom.profile != geom.profile || ((lsig0 :: upper).length != geom.numLayers)) = false := by
    rw [hWf, hPk, hNL]
    simp
  unfold verifyAggNativeSig
  simp only [hCond, Bool.false_eq_true, ↓reduceIte, hF]
  unfold verifyAggNativeSigStateless
  exact evalStatelessFlow_ok _ _ _ _ _ leaf idxs forsPk root0 pk.pkRoot hXof hFors hL0 hUp
    (beq_self_eq_true _)

/-- Row of the `DetTreeHmsgBlock0` of hypertree layer `l` in a `CorduroyPoseidon2` block. -/
def stepCordLayerRow (l : Nat) : Nat := 571 + l * 465

/-- The native signature read from the auxiliary columns of a `CorduroyPoseidon2` signer
    block: `rRand` from the `StatelessDeriveBlock1` row, the 32 FORS openings from the
    `ForsLeafHash` and `ForsMerkleBlockA` rows, and per hypertree layer the counter bits of the
    `DetTreeHmsgBlock1` row, the chain values of the `WotsChainStep0` rows and the
    authentication path of the `XmssMerkleBlockA` rows. -/
def stepCordSig (R : Nat → StepOpRow) : AggNativeSignature :=
  { profile := .corduroyPoseidon2
    rRand := stepAuxLane R 1 0
    statefulLeafIdx := 0
    forsOpenings := (List.range' 0 32).map (fun j => stepForsOpening R (stepForsRow 9 j))
    layers := (List.range' 0 16).map (fun l => stepCordLayerSig R (stepCordLayerRow l)) }

theorem stepCordLayerOps_length (layer : Nat) (isTop : Bool) :
    (stepCordLayerOps layer isTop).length = 465 := by
  unfold stepCordLayerOps
  rw [List.length_append, pushLayerWotsAndMerkle_eq, List.length_append, List.length_append,
    stepWotsOps_length]
  rfl

theorem stepForsPairOps_length (pair : Nat) : (stepForsPairOps pair).length = 35 := by
  rfl

/-- **Native-signature witness extraction, `CorduroyPoseidon2` profile.** If the 256-column
    `StepOp` table is accepted and slot `k` is active with public inputs `(pk, mu)`, `mu` the
    message representative of `msg` under `pk`, then the stateless signature read from the
    auxiliary columns of the slot's rows is accepted by the native verifier. -/
theorem stepOp256TableOk_corduroy_extract (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hTable : stepOp256TableOk .corduroyPoseidon2 slots rows = true)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .corduroyPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    verifyAggNativeSig corduroyPoseidon2Geom pub.1 msg
      (stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows k)) = true := by
  obtain ⟨R, hR⟩ : ∃ R, R = stepOpSlotRow .corduroyPoseidon2 rows k := ⟨_, rfl⟩
  rw [← hR]
  have hRun0 := stepOp256TableOk_slot_run .corduroyPoseidon2 slots rows k pub hTable hSlot
  rw [← hR] at hRun0
  have hRun : StepRunAt pub R
      ((((stepDeriveOps ++ [StepOp.forsRootsSpongeInit]) ++
          (List.range 16).flatMap stepForsPairOps) ++ [StepOp.forsRootsFinalSqueeze]) ++
        (List.range 16).flatMap (fun layer => stepCordLayerOps layer (layer + 1 == 16))) 0 :=
    hRun0
  have hDerive : StepRunAt pub R stepDeriveOps 0 :=
    hRun.append_left.append_left.append_left.append_left
  have hI : StepRowSem pub R .forsRootsSpongeInit 9 :=
    hRun.append_left.append_left.append_left.append_right.head
  have hPairs : StepRunAt pub R ((List.range 16).flatMap stepForsPairOps) (9 + 1) :=
    hRun.append_left.append_left.append_right
  have hlenPre : ((stepDeriveOps ++ [StepOp.forsRootsSpongeInit]) ++
      (List.range 16).flatMap stepForsPairOps).length = 570 := by
    rw [List.length_append, flatMap_range_uniform_length _ 35 stepForsPairOps_length]
    rfl
  have hSq : StepRowSem pub R .forsRootsFinalSqueeze (9 + 561) := by
    have h := hRun.append_left.append_right
    rw [hlenPre] at h
    exact h.head
  have hLayers : StepRunAt pub R
      ((List.range 16).flatMap (fun layer => stepCordLayerOps layer (layer + 1 == 16))) 571 := by
    have h := hRun.append_right
    rw [List.length_append, hlenPre] at h
    exact h
  have hL : ∀ l < 16, StepRunAt pub R (stepCordLayerOps l (l + 1 == 16)) (571 + l * 465) :=
    StepRunAt.flatMap_range (L := 465) (fun l => stepCordLayerOps_length l _) 16 hLayers
  obtain ⟨hLimbs, hPack, hAddr9⟩ := stepStatelessDerive_sem hDerive
  obtain ⟨m, hm⟩ : ∃ m, m = stepXofState pub R := ⟨_, rfl⟩
  obtain ⟨leaf, hleaf⟩ : ∃ leaf, leaf = stepXofLeaf m := ⟨_, rfl⟩
  rw [← hm] at hLimbs hPack hAddr9
  rw [← hleaf] at hAddr9
  obtain ⟨hIdxLt, hSlots, hRoots, hCur571, hAddr571⟩ :=
    stepFors_sem (t0 := 9) (leaf := leaf) hI hPairs hSq hAddr9
  have hCur571' : (stepRegsAt R 571).curRoot = _ := hCur571
  have hAddr571' : StepAddrOk (stepRegsAt R 571) (leaf % 16) (leaf / 16) := hAddr571
  -- The indices the rows open are the indices the XOF derives.
  have hIdxSlot : ∀ s a len : Nat, (∀ c < 32, c / 6 = s ↔ a ≤ c ∧ c < a + len) → s < 6 →
      a + len ≤ 32 → len ≤ 6 → 6 * s = a → ∀ c, a ≤ c → c < a + len →
      stepForsIdxN R (stepForsRow 9 c) = stepForsIdx m c := by
    intro s a len hRange hs haN hLen6 hStart c hac hcl
    have hLen : 256 ^ len < goldilocksPrime :=
      Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hLen6) (by decide)
    have h1 := hSlots s a len hRange hs haN hLen
    have h2 := hPack s hs
    rw [stepPackFoldG_slot 256 _ _ _ 32 s a len hRange haN hStart] at h2
    have hLtB : evalBaseDigits 256 ((List.range' a len).map (stepForsIdx m)) < 256 ^ len := by
      have h := evalBaseDigits_lt_pow 256 (by decide) ((List.range' a len).map (stepForsIdx m))
        (fun d hd => by
          obtain ⟨c', _, rfl⟩ := List.mem_map.mp hd
          exact stepForsIdx_lt m c')
      rw [List.length_map, List.length_range'] at h
      exact h
    rw [h2, Goldilocks.ofNat_val, Nat.mod_eq_of_lt (Nat.lt_trans hLtB hLen)] at h1
    have hEq := evalBaseDigits_inj 256 (by decide)
      (by rw [List.length_map, List.length_map])
      (fun d hd => by
        obtain ⟨c', _, rfl⟩ := List.mem_map.mp hd
        exact stepForsIdx_lt m c')
      (fun d hd => by
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hd
        have hb := mem_range'_bounds _ _ _ hc'
        exact hIdxLt c' (by omega))
      h1
    exact (List.map_inj_left.mp hEq c (mem_range'_of_bounds len a c hac hcl)).symm
  have hIdx : ∀ j < 32, stepForsIdxN R (stepForsRow 9 j) = stepForsIdx m j := by
    intro j hj
    by_cases h5 : j / 6 < 5
    · exact hIdxSlot (j / 6) (6 * (j / 6)) 6 (fun c hc => ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩) (by omega) (by omega)
        (Nat.le_refl _) rfl j (by omega) (by omega)
    · exact hIdxSlot (j / 6) (6 * (j / 6)) 2 (fun c hc => ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩) (by omega) (by omega)
        (by decide) rfl j (by omega) (by omega)
  -- The stateless XOF derive of the native verifier.
  have hLeafLt : leaf < 2 ^ 64 := by rw [hleaf]; unfold stepXofLeaf; omega
  have hXof : deriveStatelessLeafAndForsChecked corduroyPoseidon2Geom pub.1 (stepAuxLane R 1 0)
      pub.2 = some (leaf, (List.range' 0 32).map (stepForsIdx m)) := by
    have hAll : ([m.b0.x0, m.b0.x1, m.b0.x2, m.b0.x3, m.b1.x0, m.b1.x1, m.b1.x2].all
        (fun l => decide (l.val < 2 ^ 63))) = true := by
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨hLimbs 0 (by decide), hLimbs 1 (by decide), hLimbs 2 (by decide),
        hLimbs 3 (by decide), hLimbs 4 (by decide), hLimbs 5 (by decide),
        hLimbs 6 (by decide)⟩
    have hIdxL : (List.range 32).map (fun t =>
        ((match t / 7 with
          | 0 => m.b0.x0.val
          | 1 => m.b0.x1.val
          | 2 => m.b0.x2.val
          | 3 => m.b0.x3.val
          | _ => m.b1.x0.val) / (256 ^ (t % 7))) % 2 ^ 8) =
        (List.range' 0 32).map (stepForsIdx m) := by
      rw [← List.range_eq_range']
      apply List.map_congr_left
      intro t ht
      have ht' := List.mem_range.mp ht
      have h7 : t / 7 = 0 ∨ t / 7 = 1 ∨ t / 7 = 2 ∨ t / 7 = 3 ∨ t / 7 = 4 := by omega
      unfold stepForsIdx
      rcases h7 with h | h | h | h | h <;> rw [h] <;> rfl
    have key : deriveStatelessLeafAndForsChecked corduroyPoseidon2Geom pub.1 (stepAuxLane R 1 0)
        pub.2 =
        (if ([m.b0.x0, m.b0.x1, m.b0.x2, m.b0.x3, m.b1.x0, m.b1.x1, m.b1.x2].all
            (fun l => decide (l.val < 2 ^ 63))) = true then
          some (stepXofLeaf m % 2 ^ 64, (List.range 32).map (fun t =>
            ((match t / 7 with
              | 0 => m.b0.x0.val
              | 1 => m.b0.x1.val
              | 2 => m.b0.x2.val
              | 3 => m.b0.x3.val
              | _ => m.b1.x0.val) / (256 ^ (t % 7))) % 2 ^ 8))
        else none) := by
      rw [hm]
      rfl
    rw [key, hIdxL, hAll, ← hleaf, Nat.mod_eq_of_lt hLeafLt]
    rfl
  -- The FORS public key.
  have hFors : verifyAndRecoverForsPk corduroyPoseidon2Geom pub.1.pkSeed leaf
      ((List.range' 0 32).map (stepForsIdx m))
      ((List.range' 0 32).map (fun j => stepForsOpening R (stepForsRow 9 j))) =
      some (stepRegsAt R 571).curRoot := by
    have hAux : verifyForsTreesAux corduroyPoseidon2Geom pub.1.pkSeed leaf 0
        ((List.range' 0 32).map (stepForsIdx m))
        ((List.range' 0 32).map (fun j => stepForsOpening R (stepForsRow 9 j))) =
        some ((List.range' 0 32).map (stepForsRoot R 9)) := by
      unfold verifyForsTreesAux
      exact verifyForsPoly_map _ _ _ _ 32 0 (fun i _ hi => by
        have h := hRoots i (by omega)
        rw [hIdx i (by omega)] at h
        exact h)
    unfold verifyAndRecoverForsPk
    simp only [List.length_map, List.length_range', hAux]
    rw [hCur571', List.range_eq_range']
    rfl
  -- The hypertree layers.
  have hInv : ∀ l, l < 16 →
      StepAddrOk (stepRegsAt R (571 + l * 465)) ((leaf / 16 ^ l) % 16) (leaf / 16 ^ (l + 1)) := by
    intro l
    induction l with
    | zero =>
      intro _
      have e : 571 + 0 * 465 = 571 := by omega
      rw [e, Nat.pow_zero, Nat.div_one, Nat.pow_one]
      exact hAddr571'
    | succ l ih =>
      intro hl
      have hA := ih (by omega)
      have hRunL := hL l (by omega)
      rw [beq_false_of_ne (by omega : l + 1 ≠ 16)] at hRunL
      obtain ⟨_, _, hLink⟩ := stepCordLayer_sem hRunL hA (by omega)
        (Nat.mod_lt _ (by decide))
      obtain ⟨hA', _⟩ := hLink rfl
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLeafLt)
      have e : 571 + (l + 1) * 465 = 571 + l * 465 + 465 := by omega
      have e2 : leaf / 16 ^ (l + 1 + 1) = leaf / 16 ^ (l + 1) / 16 := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      rw [e, e2]
      exact hA'
  obtain ⟨cur, hcur⟩ : ∃ cur : Nat → Digest4, cur = fun l => match l with
      | 0 => (stepRegsAt R 571).curRoot
      | l + 1 => (stepPermAt R (571 + l * 465 + 464)).b0 := ⟨_, rfl⟩
  have hCurRow : ∀ l, l < 16 → (stepRegsAt R (571 + l * 465)).curRoot = cur l := by
    intro l hl
    rcases l with _ | l
    · rw [hcur]
    · have hRunL := hL l (by omega)
      rw [beq_false_of_ne (by omega : l + 1 ≠ 16)] at hRunL
      obtain ⟨_, _, hLink⟩ := stepCordLayer_sem hRunL (hInv l (by omega)) (by omega)
        (Nat.mod_lt _ (by decide))
      obtain ⟨_, hC⟩ := hLink rfl
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hLeafLt)
      have e : 571 + (l + 1) * 465 = 571 + l * 465 + 465 := by omega
      rw [e, hC, hcur]
  have hLayerV : ∀ l, l < 16 →
      verifyWotsLayer corduroyPoseidon2Geom pub.1 l
          (leaf / 16 ^ l / 2 ^ corduroyPoseidon2Geom.subtreeHeight)
          (leaf / 16 ^ l % 2 ^ corduroyPoseidon2Geom.subtreeHeight)
          (computeHmsgDetTree pub.1 l (leaf / 16 ^ l / 2 ^ corduroyPoseidon2Geom.subtreeHeight)
            (leaf / 16 ^ l % 2 ^ corduroyPoseidon2Geom.subtreeHeight)
            (stepCordLayerSig R (stepCordLayerRow l)).tswCtr (cur l))
          (stepCordLayerSig R (stepCordLayerRow l)) = some (cur (l + 1)) := by
    intro l hl
    obtain ⟨hV, _, _⟩ := stepCordLayer_sem (hL l hl) (hInv l hl) hl (Nat.mod_lt _ (by decide))
    have e2 : leaf / 16 ^ l / 2 ^ corduroyPoseidon2Geom.subtreeHeight = leaf / 16 ^ (l + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      rfl
    have e3 : leaf / 16 ^ l % 2 ^ corduroyPoseidon2Geom.subtreeHeight = leaf / 16 ^ l % 16 := rfl
    rw [e2, e3, ← hCurRow l hl]
    have e4 : cur (l + 1) = (stepPermAt R (571 + l * 465 + 464)).b0 := by rw [hcur]
    rw [e4]
    exact hV
  have hTop : cur 16 = pub.1.pkRoot := by
    obtain ⟨_, hT, _⟩ := stepCordLayer_sem (hL 15 (by decide)) (hInv 15 (by decide))
      (by decide) (Nat.mod_lt _ (by decide))
    rw [hcur]
    exact hT rfl
  have hUp := verifyUpperLayers_chain corduroyPoseidon2Geom pub.1
    (fun l => stepCordLayerSig R (stepCordLayerRow l)) cur (fun l => leaf / 16 ^ l) 15 1
    (fun l _ h2 => ⟨hLayerV l (by omega), by
      show leaf / 16 ^ (l + 1) = leaf / 16 ^ l / 2 ^ corduroyPoseidon2Geom.subtreeHeight
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      rfl⟩)
  have hL0 := hLayerV 0 (by decide)
  rw [Nat.pow_zero, Nat.div_one] at hL0
  have hUp' : verifyUpperLayers corduroyPoseidon2Geom pub.1 1
      (leaf / 2 ^ corduroyPoseidon2Geom.subtreeHeight) (cur 1)
      ((List.range' 1 15).map (fun l => stepCordLayerSig R (stepCordLayerRow l))) =
      some pub.1.pkRoot := by
    rw [← hTop]
    exact hUp
  have hCur0 : cur 0 = (stepRegsAt R 571).curRoot := by rw [hcur]
  rw [hCur0] at hL0
  rw [hMu] at hXof
  exact verifyAggNativeSig_stateless_intro corduroyPoseidon2Geom pub.1 msg (stepAuxLane R 1 0)
    _ (stepCordLayerSig R (stepCordLayerRow 0))
    ((List.range' 1 15).map (fun l => stepCordLayerSig R (stepCordLayerRow l)))
    leaf _ _ (cur 1) (by decide) hProf rfl rfl hXof hFors hL0 hUp'

/-- Executable decision and witness extraction for an active stateless slot. The success
    branch contains the native signature itself. -/
def extractCorduroySlotOrReject (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .corduroyPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    PSum { sig : AggNativeSignature //
        verifyAggNativeSig corduroyPoseidon2Geom pub.1 msg sig = true }
      (stepOp256TableOk .corduroyPoseidon2 slots rows = false) :=
  if h : stepOp256TableOk .corduroyPoseidon2 slots rows = true then
    .inl ⟨stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows k),
      stepOp256TableOk_corduroy_extract slots rows k pub msg h hSlot hProf hMu⟩
  else .inr (Bool.eq_false_iff.mpr h)

/-- The rows of each hypertree layer inside a `CorduroyPoseidon2` signer block. -/
private theorem stepCordRun_layer {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    (hRun0 : StepRunAt pub R (signerProgramBody .corduroyPoseidon2) 0) :
    ∀ l < 16, StepRunAt pub R (stepCordLayerOps l (l + 1 == 16)) (571 + l * 465) := by
  have hRun : StepRunAt pub R
      ((((stepDeriveOps ++ [StepOp.forsRootsSpongeInit]) ++
          (List.range 16).flatMap stepForsPairOps) ++ [StepOp.forsRootsFinalSqueeze]) ++
        (List.range 16).flatMap (fun layer => stepCordLayerOps layer (layer + 1 == 16))) 0 :=
    hRun0
  have hlenPre : ((stepDeriveOps ++ [StepOp.forsRootsSpongeInit]) ++
      (List.range 16).flatMap stepForsPairOps).length = 570 := by
    rw [List.length_append, flatMap_range_uniform_length _ 35 stepForsPairOps_length]
    rfl
  have hLayers : StepRunAt pub R
      ((List.range 16).flatMap (fun layer => stepCordLayerOps layer (layer + 1 == 16))) 571 := by
    have h := hRun.append_right
    rw [List.length_append, hlenPre] at h
    exact h
  exact StepRunAt.flatMap_range (L := 465) (fun l => stepCordLayerOps_length l _) 16 hLayers

/-- A stateless block whose last Merkle row does not hash to the public-key root is rejected:
    the extraction theorem's acceptance hypothesis is sensitive to the top-layer root. -/
theorem tooth_stepOp256_corduroy_wrong_top_root_rejected (slots : List StepOpSlot)
    (rows : List StepOpRow) (k : Nat) (pub : AggValidatorPk × Digest5)
    (hSlot : slots[k]? = some (some pub))
    (hWrong : (poseidon2Perm12 (stepOpSlotRow .corduroyPoseidon2 rows k 8010).stIn).b0 ≠
      pub.1.pkRoot) :
    stepOp256TableOk .corduroyPoseidon2 slots rows = false := by
  apply Bool.eq_false_iff.mpr
  intro hTable
  have hRun0 := stepOp256TableOk_slot_run .corduroyPoseidon2 slots rows k pub hTable hSlot
  have hTop : StepRowSem pub (stepOpSlotRow .corduroyPoseidon2 rows k)
      (.xmssMerkleBlockB true true) 8010 :=
    (stepCordRun_layer hRun0 15 (by decide)).get 464 _ rfl
  exact hWrong (stepSem_xmssMerkleBlockB_top hTop).2.2

#tooth_pair stepOp256TableOk_corduroy_extract vs tooth_stepOp256_corduroy_wrong_top_root_rejected

/-- Read every stateless signature from its accepted machine block in committee order. -/
def corduroyCommitteeSigs (stmt : AggArithPublicStmt) (rows : List StepOpRow) :
    List AggNativeSignature :=
  (List.range stmt.committeePks.length).map
    (fun k => stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows k))

/-- Whole-committee soundness of the stateless machine extractor. -/
theorem corduroyCommitteeSigs_valid (stmt : AggArithPublicStmt) (rows : List StepOpRow)
    (hGeom : stmt.geom = corduroyPoseidon2Geom) (hWf : stmt.wellFormed = true)
    (hTable : stepOp256TableOk .corduroyPoseidon2 (xmssCommitteeSlots stmt) rows = true) :
    (corduroyCommitteeSigs stmt rows).length = stmt.committeePks.length ∧
    ∀ (k : Nat) (hkP : k < stmt.committeePks.length)
      (hkS : k < (corduroyCommitteeSigs stmt rows).length),
      verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
        ((corduroyCommitteeSigs stmt rows)[k]'hkS) = true := by
  refine ⟨by simp [corduroyCommitteeSigs], ?_⟩
  intro k hkP hkS
  have hpks : stmt.committeePks.all (·.profile == stmt.geom.profile) = true :=
    (Bool.and_eq_true_iff.mp hWf).2
  have hp : (stmt.committeePks[k]'hkP).profile = .corduroyPoseidon2 := by
    have h := eq_of_beq (List.all_eq_true.mp hpks _ (List.getElem_mem hkP))
    simpa only [hGeom, corduroyPoseidon2Geom] using h
  have hs : (xmssCommitteeSlots stmt)[k]? =
      some (some (stmt.committeePks[k]'hkP, computeMessageMu (stmt.committeePks[k]'hkP) stmt.msg)) := by
    simp [xmssCommitteeSlots, List.getElem?_eq_getElem hkP]
  simpa [corduroyCommitteeSigs, hGeom] using
    stepOp256TableOk_corduroy_extract (xmssCommitteeSlots stmt) rows k
      (stmt.committeePks[k]'hkP, computeMessageMu (stmt.committeePks[k]'hkP) stmt.msg)
      stmt.msg hTable hs hp rfl

/-- Construct the serialized trace from the machine-extracted stateless signatures. -/
def corduroyMachineToExecutionTrace (stmt : AggArithPublicStmt) (rows : List StepOpRow) :
    AggExecutionTrace := buildHonestAggExecutionTrace stmt (corduroyCommitteeSigs stmt rows)

/-- **256-column to serialized-trace bridge, stateless profile.** An accepted 256-column table
    over the committee's active slots yields an accepted serialized execution trace. -/
theorem corduroyMachineToExecutionTrace_accepts (stmt : AggArithPublicStmt)
    (rows : List StepOpRow)
    (hGeom : stmt.geom = corduroyPoseidon2Geom) (hWf : stmt.wellFormed = true)
    (hTable : stepOp256TableOk .corduroyPoseidon2 (xmssCommitteeSlots stmt) rows = true) :
    traceSatisfiesAllConstraints stmt (corduroyMachineToExecutionTrace stmt rows) = true := by
  obtain ⟨hLen, hAll⟩ := corduroyCommitteeSigs_valid stmt rows hGeom hWf hTable
  exact buildHonestAggExecutionTrace_satisfies_constraints stmt _ hWf hLen hAll

end HemStepOp256Machine

/-! ## §4. Forward direction: a native `XmssPoseidon2` signature yields an accepted table -/

section StepOpForward

local infixl:65 " +ₚ " => Goldilocks.add
local infixl:70 " *ₚ " => Goldilocks.mul
local notation "‹" n "›" => Goldilocks.ofNat n

/-- An instruction's free cells. The interpreter supplies all other columns. -/
structure StepForwardCells where
  input : Poseidon2State12
  aux : Fin 38 → Goldilocks

/-- Execute one instruction with honest permutation columns. -/
def stepForwardRow (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) : StepOpRow :=
  populateStepOpNext (stepOpKindAndC0 op).1 (Goldilocks.ofNat (stepOpKindAndC0 op).2) pub
    (stepOpHonestPermutationRow cells.input prev [] (List.ofFn cells.aux))

/-- Execute a list of instructions, passing the entire next state to the following row. -/
def stepForwardRun (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) :
    List StepOp → List Goldilocks → List StepOpRow
  | [], _ => []
  | op :: ops, prev =>
    let row := stepForwardRow pub op prev (supply op prev)
    row :: stepForwardRun pub supply ops row.nextState

theorem stepForwardRun_length (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) :
    (stepForwardRun pub supply ops prev).length = ops.length := by
  induction ops generalizing prev with
  | nil => rfl
  | cons op ops ih => simp only [stepForwardRun, List.length_cons, ih]

theorem stepForwardRow_groupA (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) :
    allZeroGoldilocks (stepOpPermTrace (stepForwardRow pub op prev cells)).2 = true :=
  stepOpHonestPermutationRow_groupA cells.input prev _ _

theorem stepForwardRow_perm (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) :
    (stepOpPermTrace (stepForwardRow pub op prev cells)).1 = poseidon2Perm12 cells.input :=
  stepOp256_groupA_exact _ (stepForwardRow_groupA pub op prev cells)

theorem stepForwardRow_next_length (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) :
    (stepForwardRow pub op prev cells).nextState.length = 44 := by
  simp only [stepForwardRow, populateStepOpNext, List.length_map, List.length_range]

theorem stepForwardRow_wellShaped (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells) (hp : prev.length = 44) :
    (stepForwardRow pub op prev cells).wellShaped = true :=
  stepOpHonestPermutationRow_wellShaped cells.input prev _ _ hp
    (stepForwardRow_next_length pub op prev cells) List.length_ofFn

/-- All opcode converses share this transition constructor; only the guards remain. -/
theorem stepForwardRow_constraints_iff (pub : AggValidatorPk × Digest5) (op : StepOp)
    (prev : List Goldilocks) (cells : StepForwardCells)
    (hv : (stepOpKindAndC0 op).1.validSlot = true) :
    allZeroGoldilocks (stepOpConstraints (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs pub (stepForwardRow pub op prev cells))) = true ↔
    allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs pub (stepOpHonestPermutationRow cells.input prev []
        (List.ofFn cells.aux)))) = true :=
  populateStepOpNext_constraints_iff _ _ _ _ hv

theorem stepForwardRun_wellShaped (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) (hp : prev.length = 44) :
    ∀ row ∈ stepForwardRun pub supply ops prev, row.wellShaped = true := by
  induction ops generalizing prev with
  | nil => simp [stepForwardRun]
  | cons op ops ih =>
    intro row hr
    simp only [stepForwardRun, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact stepForwardRow_wellShaped _ _ _ _ hp
    · exact ih _ (stepForwardRow_next_length ..) _ hr

theorem stepForwardRun_groupA (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) :
    ∀ row ∈ stepForwardRun pub supply ops prev,
      allZeroGoldilocks (stepOpPermTrace row).2 = true := by
  induction ops generalizing prev with
  | nil => simp [stepForwardRun]
  | cons op ops ih =>
    intro row hr
    simp only [stepForwardRun, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact stepForwardRow_groupA ..
    · exact ih _ _ hr

theorem stepForwardRun_first (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) (row : StepOpRow)
    (h : (stepForwardRun pub supply ops prev)[0]? = some row) :
    row.prevState = prev := by
  cases ops with
  | nil => simp [stepForwardRun] at h
  | cons op ops =>
    simp only [stepForwardRun, List.getElem?_cons_zero, Option.some.injEq] at h
    subst row
    rfl

theorem stepForwardRun_shift (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) :
    ∀ i r r', (stepForwardRun pub supply ops prev)[i]? = some r →
      (stepForwardRun pub supply ops prev)[i + 1]? = some r' →
      r.nextState = r'.prevState := by
  induction ops generalizing prev with
  | nil => simp [stepForwardRun]
  | cons op ops ih =>
    intro i r r' hr hr'
    cases i with
    | zero =>
      simp only [stepForwardRun, List.getElem?_cons_zero, Option.some.injEq] at hr
      subst r
      exact (stepForwardRun_first _ _ _ _ _ hr').symm
    | succ i =>
      simp only [stepForwardRun, List.getElem?_cons_succ] at hr hr'
      exact ih _ i r r' hr hr'

/-- Recover the exact instruction and incoming state used to build a row. -/
theorem stepForwardRun_at (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells)
    (ops : List StepOp) (prev : List Goldilocks) :
    ∀ (i : Nat) row, (stepForwardRun pub supply ops prev)[i]? = some row →
      ∃ op state, ops[i]? = some op ∧
        row = stepForwardRow pub op state (supply op state) := by
  induction ops generalizing prev with
  | nil => simp [stepForwardRun]
  | cons op ops ih =>
    intro i row hr
    cases i with
    | zero =>
      simp only [stepForwardRun, List.getElem?_cons_zero, Option.some.injEq] at hr
      exact ⟨op, prev, rfl, hr.symm⟩
    | succ i =>
      simp only [stepForwardRun, List.getElem?_cons_succ] at hr
      exact ih _ i row hr


/-- Zero register file used at every signer boundary. -/
def stepForwardZero : List Goldilocks := List.replicate 44 Goldilocks.zero

/-- Execute the padded program of a signer. -/
def stepForwardBlock (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) : List StepOpRow :=
  stepForwardRun pub supply (buildSignerProgram profile) stepForwardZero

theorem stepForwardBlock_length (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) :
    (stepForwardBlock profile pub supply).length = stepOpRowsPerSigner profile := by
  rw [stepForwardBlock, stepForwardRun_length]
  cases profile
  · exact buildSignerProgram_length.2.2.1
  · exact buildSignerProgram_length.2.2.2

/-- Every signer program ends with an idle instruction, which clears all registers. -/
theorem stepForwardProgram_last (profile : AggSigProfile) :
    (buildSignerProgram profile).getD (stepOpRowsPerSigner profile - 1) .idle = .idle := by
  cases profile <;> decide +kernel

theorem stepForwardBlock_boundary (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) (i : Nat) (row : StepOpRow)
    (hr : (stepForwardBlock profile pub supply)[i]? = some row) :
    allZeroGoldilocks (stepOpBoundaryResiduals (stepOpRowsPerSigner profile) i row) = true := by
  apply (stepOpBoundaryResiduals_iff _ _ _).mpr
  constructor
  · intro j _ hi
    subst i
    have hp := stepForwardRun_first pub supply (buildSignerProgram profile) stepForwardZero row hr
    rw [hp]
    exact getD_replicate_zero 44 j
  · intro j hj hi
    obtain ⟨op, state, hop, rfl⟩ := stepForwardRun_at pub supply
      (buildSignerProgram profile) stepForwardZero i row hr
    have hi' : i = stepOpRowsPerSigner profile - 1 := by omega
    have hop' : op = .idle := by
      have h := stepForwardProgram_last profile
      rw [← hi', List.getD_eq_getElem?_getD, hop] at h
      exact h
    subst op
    change ((List.range 44).map (fun _ => Goldilocks.zero)).getD j Goldilocks.zero = _
    simp [List.getD_eq_getElem?_getD, hj]

/-- The complete interpreter satisfies the table checker exactly when its guards hold.
    Shape, permutation witnesses, boundary resets, and shifts need no hypotheses. -/
theorem stepForwardBlock_table_iff (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (supply : StepOp → List Goldilocks → StepForwardCells) :
    stepOp256TableOk profile [some pub] (stepForwardBlock profile pub supply) = true ↔
    ∀ i row, (stepForwardBlock profile pub supply)[i]? = some row →
      allZeroGoldilocks (stepOpGuardResiduals
        (stepOpKindAndC0 ((buildSignerProgram profile).getD i .idle)).1
        (Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD i .idle)).2)
        (stepOpRowInputs pub row)) = true := by
  rw [stepOp256TableOk_iff_rows]
  have hn := stepForwardBlock_length profile pub supply
  have index : ∀ i row, (stepForwardBlock profile pub supply)[i]? = some row →
      i / stepOpRowsPerSigner profile = 0 ∧ i % stepOpRowsPerSigner profile = i := by
    intro i row hr
    have hi := (List.getElem?_eq_some_iff.mp hr).1
    rw [hn] at hi
    exact ⟨Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi⟩
  constructor
  · intro h i row hr
    obtain ⟨hd, hm⟩ := index i row hr
    have hz := h.2.2.2.1 i row hr
    simp only [hd, hm, List.getD_cons_zero] at hz
    exact ((stepOp256RowResiduals_active_iff profile pub i row).mp hz).2.2.2.1
  · intro hg
    refine ⟨by simp, by simpa using hn,
      stepForwardRun_wellShaped pub supply _ _ (List.length_replicate ..), ?_, ?_⟩
    · intro i row hr
      obtain ⟨hd, hm⟩ := index i row hr
      simp only [hd, hm, List.getD_cons_zero]
      unfold stepOp256RowResiduals
      rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true]
      refine ⟨⟨stepForwardRun_groupA pub supply _ _ row (List.mem_of_getElem? hr),
        stepForwardBlock_boundary profile pub supply i row hr⟩, ?_⟩
      obtain ⟨op, state, hop, he⟩ := stepForwardRun_at pub supply
        (buildSignerProgram profile) stepForwardZero i row hr
      have hopD : (buildSignerProgram profile).getD i .idle = op := by
        rw [List.getD_eq_getElem?_getD, hop]; rfl
      have hv := (buildSignerProgram_kind_mem_and_valid profile i).2
      rw [hopD] at hv ⊢
      apply (stepOpConstraints_iff_guard_and_next _ _ _ hv).mpr
      refine ⟨by simpa only [hopD] using hg i row hr, ?_⟩
      subst row
      intro j hj
      rw [stepForwardRow, populateStepOpNext_inputs, stepOpExpectedNext_congr_next]
      simp [stepOpRowInputs, List.getD_eq_getElem?_getD, hj]
    · intro i r r' hr hr' j _
      rw [stepForwardRun_shift pub supply _ _ i r r' hr hr']

/-- Read a four-limb auxiliary block, using zero for absent signature elements. -/
def stepForwardLane (f : Nat → Goldilocks) (base : Nat) : Lane4 :=
  ⟨f base, f (base + 1), f (base + 2), f (base + 3)⟩

/-- Auxiliary cells for the XMSS program. Out-of-profile instructions receive zeros. -/
def stepXmssAux (sig : AggNativeSignature) (op : StepOp)
    (prev : List Goldilocks) (i : Nat) : Goldilocks :=
  let ls := sig.layers.getD 0 ⟨0, [], []⟩
  let s := fun j => prev.getD j Goldilocks.zero
  match op with
  | .statefulHmsgBlock0 =>
    if i < 6 then Goldilocks.ofNat (sig.statefulLeafIdx / 2 ^ i % 2)
    else if i < 38 then Goldilocks.ofNat (ls.tswCtr / 2 ^ (i - 6) % 2)
    else Goldilocks.zero
  | .statefulHmsgBlock1 => sig.rRand.toList.getD i Goldilocks.zero
  | .hmsgDecompLimb l =>
    if i < 31 then Goldilocks.ofNat ((s (stMainSponge + l)).val / 4 ^ i % 4)
    else if i = 31 then Goldilocks.ofNat ((s (stMainSponge + l)).val / 2 ^ 62 % 2)
    else Goldilocks.zero
  | .wotsChainStep0 _ chain slot =>
    let rem := (s (stRemPack + slot)).val
    let digit := 3 - rem % 4
    if i < 4 then (ls.wotsChains.getD chain lane4Zero).toList.getD i Goldilocks.zero
    else if i < 7 then Goldilocks.ofNat (if i - 4 < digit then 1 else 0)
    else if i = 7 then Goldilocks.ofNat (rem / 4)
    else Goldilocks.zero
  | .xmssMerkleBlockA _ lvl =>
    if i = 0 then Goldilocks.ofNat ((s stCursorIdx).val % 2)
    else if i = 1 then Goldilocks.ofNat ((s stCursorIdx).val / 2)
    else if i < 6 then
      (ls.merklePath.getD lvl lane4Zero).toList.getD (i - 2) Goldilocks.zero
    else Goldilocks.zero
  | _ => Goldilocks.zero

/-- Permutation inputs for the XMSS program, expressed using the actual incoming registers. -/
def stepXmssInput (pk : AggValidatorPk) (mu : Digest5) (op : StepOp)
    (prev : List Goldilocks) (aux : Nat → Goldilocks) : Poseidon2State12 :=
  let r := stepRegs (fun j => prev.getD j Goldilocks.zero)
  let c0 := Goldilocks.ofNat (stepOpKindAndC0 op).2
  match op with
  | .statefulHmsgBlock0 =>
    ⟨pk.pkSeed, pk.pkRoot, ⟨domainHMsgStateful,
      stepWeightedSum aux (fun i => 2 ^ i) 6 *ₚ Goldilocks.ofNat (2 ^ 32) +ₚ
        stepWeightedSum (fun i => aux (6 + i)) (fun i => 2 ^ i) 32,
      mu.limb4, poseidon2IvTag⟩⟩
  | .statefulHmsgBlock1 =>
    ⟨lane4Add r.main.b0 (stepForwardLane aux 0),
      lane4Add r.main.b1 ⟨mu.limb0, mu.limb1, mu.limb2, mu.limb3⟩, r.main.b2⟩
  | .statefulHmsgSqueeze | .wotsTellFinalSqueeze => stepSqueezeIn r
  | .wotsTellInit _ =>
    ⟨pk.pkSeed, ⟨c0 +ₚ r.kp, r.treeLo, r.treeHi, Goldilocks.ofNat 128⟩,
      ⟨domainWotsPk, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩
  | .wotsChainStep0 _ _ _ =>
    ⟨stepForwardLane aux 0, pk.pkSeed,
      ⟨domainWotsStep, c0 +ₚ r.kp *ₚ Goldilocks.ofNat (2 ^ 16), r.treeLo, r.treeHi⟩⟩
  | .wotsChainStep1 _ _ | .wotsChainStep2 _ _ _ =>
    ⟨r.work, pk.pkSeed,
      ⟨domainWotsStep, c0 +ₚ r.kp *ₚ Goldilocks.ofNat (2 ^ 16), r.treeLo, r.treeHi⟩⟩
  | .wotsTellPairAbsorb _ =>
    ⟨lane4Add r.main.b0 r.sub.b0, lane4Add r.main.b1 r.work, r.main.b2⟩
  | .xmssMerkleBlockA _ _ =>
    ⟨pk.pkSeed, lane4MuxL (aux 0) r.work (stepForwardLane aux 2),
      ⟨domainMerkleNode, c0 +ₚ aux 1, r.treeLo, r.treeHi⟩⟩
  | .xmssMerkleBlockB _ _ => stepMerkleBIn r
  | _ => state12Zero

/-- Signature-driven free columns for a single XMSS instruction. -/
def stepXmssCells (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) : StepForwardCells :=
  ⟨stepXmssInput pk mu op prev (stepXmssAux sig op prev),
    fun i => stepXmssAux sig op prev i.val⟩

/-- The explicit 512-row XMSS signer block, including honest padding permutations. -/
def stepXmssRows (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) : List StepOpRow :=
  stepForwardBlock .xmssPoseidon2 (pk, mu) (stepXmssCells pk mu sig)

theorem stepXmssRows_length (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    (stepXmssRows pk mu sig).length = 512 :=
  stepForwardBlock_length ..

theorem stepXmssRows_wellShaped (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    ∀ row ∈ stepXmssRows pk mu sig, row.wellShaped = true :=
  stepForwardRun_wellShaped _ _ _ _ (List.length_replicate ..)

theorem stepXmssRows_groupA (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    ∀ row ∈ stepXmssRows pk mu sig, allZeroGoldilocks (stepOpPermTrace row).2 = true :=
  stepForwardRun_groupA _ _ _ _

theorem stepXmssRows_shift (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    allZeroGoldilocks (stepOp256ShiftResiduals (stepXmssRows pk mu sig)) = true := by
  apply (stepOp256ShiftResiduals_iff _).mpr
  intro i r r' hr hr' j _
  rw [stepForwardRun_shift (pk, mu) (stepXmssCells pk mu sig) _ _ i r r' hr hr']

/-- The exact remaining obligation for native-to-machine completeness. -/
def StepXmssGuards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) : Prop :=
  ∀ (i : Nat) row, (stepXmssRows pk mu sig)[i]? = some row →
    allZeroGoldilocks (stepOpGuardResiduals
      (stepOpKindAndC0 ((buildSignerProgram .xmssPoseidon2).getD i .idle)).1
      (Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram .xmssPoseidon2).getD i .idle)).2)
      (stepOpRowInputs (pk, mu) row)) = true

theorem stepXmssRows_table_iff (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    stepOp256TableOk .xmssPoseidon2 [some (pk, mu)] (stepXmssRows pk mu sig) = true ↔
      StepXmssGuards pk mu sig :=
  stepForwardBlock_table_iff ..

/-- Directly supplied cells of an XMSS instruction, before filling the next state. -/
def stepXmssSeedRow (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) : StepOpRow :=
  stepOpHonestPermutationRow (stepXmssCells pk mu sig op prev).input prev []
    (List.ofFn (stepXmssCells pk mu sig op prev).aux)

/-- Opcodes whose guards impose no additional arithmetic or terminal checks. -/
def StepXmssPlainOp : StepOp → Prop
  | .idle | .statefulHmsgBlock1 | .statefulHmsgSqueeze | .wotsTellInit _
  | .wotsChainStep1 _ _ | .wotsChainStep2 _ _ _ | .wotsTellFinalSqueeze
  | .xmssMerkleBlockB false _ => True
  | _ => False

macro "step_forward_reduce" : tactic => `(tactic|
  simp only [stepOpKindAndC0, stepOpGuardResiduals,
    stepSpongeAbsorbInput, stepSqueezeInput, stepWotsStepInput, stepMerkleBlockBInput,
    stepOpRowInputs, stepXmssSeedRow, stepOpHonestPermutationRow, stepXmssCells,
    stepXmssInput, stepXmssAux, stepRegs, stepForwardLane, stepSqueezeIn, stepMerkleBIn,
    stMainSponge, stWork, stSubSponge, stTreeLo, stTreeHi, stKpIdx,
    List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.nil_append,
    List.append_nil, List.cons_append, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    List.getElem?_ofFn, Option.getD_some, Option.getD_none,
    Poseidon2State12.toList, Lane4.toList, lane4Add, lane4MuxL,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceBEq, Nat.reduceEqDiff,
    ↓reduceIte, Bool.false_eq_true, Bool.not_false, Bool.true_eq,
    g_sub_self, allZeroGoldilocks, List.all_cons, List.all_nil,
    beq_self_eq_true, Bool.and_true, Bool.true_and, dite_true] )

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_plain_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) (hop : StepXmssPlainOp op) :
    allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev))) = true := by
  cases op <;> simp only [StepXmssPlainOp] at hop
  all_goals first | contradiction | skip
  case' xmssMerkleBlockB a b => cases a <;> simp only [StepXmssPlainOp] at hop
  all_goals first | contradiction | skip
  all_goals step_forward_reduce

/-- An inactive row still has honest Group A columns and zero boundary registers. -/
def stepInactiveRow : StepOpRow :=
  stepOpHonestPermutationRow state12Zero stepForwardZero stepForwardZero
    (List.replicate 38 Goldilocks.zero)

/-- Inactive signer blocks contain real permutation witnesses, not all-zero rows. -/
def stepInactiveRows (profile : AggSigProfile) : List StepOpRow :=
  List.replicate (stepOpRowsPerSigner profile) stepInactiveRow

theorem stepInactiveRow_residuals (profile : AggSigProfile) (t : Nat) :
    allZeroGoldilocks (stepOp256RowResiduals profile none t stepInactiveRow) = true := by
  unfold stepOp256RowResiduals
  rw [List.append_nil, allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨stepOpHonestPermutationRow_groupA .., ?_⟩
  apply (stepOpBoundaryResiduals_iff _ _ _).mpr
  exact ⟨fun j _ _ => getD_replicate_zero 44 j, fun j _ _ => getD_replicate_zero 44 j⟩

/-- A nonempty committee consisting entirely of inactive slots is accepted. -/
theorem stepInactiveCommittee_table (profile : AggSigProfile) (n : Nat) (hn : 0 < n) :
    stepOp256TableOk profile (List.replicate n none)
      (List.replicate (n * stepOpRowsPerSigner profile) stepInactiveRow) = true := by
  apply (stepOp256TableOk_iff_rows _ _ _).mpr
  refine ⟨by simpa using hn, by simp, ?_, ?_, ?_⟩
  · intro row hr
    have he := (List.mem_replicate.mp hr).2
    subst row
    exact stepOpHonestPermutationRow_wellShaped _ _ _ _
      (List.length_replicate ..) (List.length_replicate ..) (List.length_replicate ..)
  · intro i row hr
    have he := (List.mem_replicate.mp (List.mem_of_getElem? hr)).2
    subst row
    have hs : (List.replicate n (none : StepOpSlot)).getD
        (i / stepOpRowsPerSigner profile) none = none := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    rw [hs]
    exact stepInactiveRow_residuals _ _
  · intro i r r' hr hr' j _
    have he := (List.mem_replicate.mp (List.mem_of_getElem? hr)).2
    have he' := (List.mem_replicate.mp (List.mem_of_getElem? hr')).2
    subst r
    subst r'
    rfl

/-- Conditional round trip through the existing native extractor. -/
theorem stepXmssRows_extract (pk : AggValidatorPk) (msg : List UInt8)
    (sig : AggNativeSignature) (hp : pk.profile = .xmssPoseidon2)
    (hg : StepXmssGuards pk (computeMessageMu pk msg) sig) :
    verifyAggNativeSig xmssPoseidon2Geom pk msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2
        (stepXmssRows pk (computeMessageMu pk msg) sig) 0)) = true :=
  stepOp256TableOk_xmss_extract _ _ 0 (pk, computeMessageMu pk msg) msg
    ((stepXmssRows_table_iff ..).mpr hg) rfl hp rfl

theorem stepXmssSeedRow_aux (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) (i : Nat) (hi : i < 38) :
    (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev)).aux i =
      stepXmssAux sig op prev i := by
  change (List.ofFn (fun j : Fin 38 => stepXmssAux sig op prev j.val)).getD i Goldilocks.zero = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]

/-- The decomposition cells satisfy the full limb gate whenever the native range check holds. -/
theorem stepXmss_limb63 (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (l : Nat)
    (h : (prev.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63) :
    allZeroGoldilocks (stepLimb63Decomp
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev)) l) = true := by
  apply (stepLimb63Decomp_allZero_iff _ _).mpr
  refine ⟨h, ?_, ?_⟩
  · intro i hi
    rw [stepXmssSeedRow_aux _ _ _ _ _ _ (by omega)]
    simp only [stepXmssAux, hi, ↓reduceIte]
    rfl
  · rw [stepXmssSeedRow_aux _ _ _ _ _ _ (by decide)]
    change Goldilocks.ofNat ((prev.getD (stMainSponge + l) Goldilocks.zero).val / 2 ^ 62 % 2) =
      Goldilocks.ofNat ((prev.getD (stMainSponge + l) Goldilocks.zero).val / 4 ^ 31)
    have he : (4 : Nat) ^ 31 = 2 ^ 62 := by decide +kernel
    rw [he, Nat.mod_eq_of_lt (by omega)]

/-- Hmsg decomposition has only the range and final digit-sum obligations. -/
theorem stepXmss_decomp_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (l : Nat)
    (h : (prev.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63)
    (hs : l = 4 → stepHmsgDecompExpected
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev))
        l stAccOrU1 = Goldilocks.ofNat 192) :
    allZeroGoldilocks (stepOpGuardResiduals (.hmsgDecompLimb l) (Goldilocks.ofNat 0)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev))) = true := by
  unfold stepOpGuardResiduals
  rw [allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨stepXmss_limb63 pk mu sig prev l h, ?_⟩
  by_cases hl : l = 4
  · simp only [ite_eq_left hl, hs hl, allZeroGoldilocks, List.all_cons, List.all_nil,
      g_sub_self, beq_self_eq_true, Bool.and_self]
  · simp [hl, allZeroGoldilocks]

/-- Canonical quotient and remainder also reconstruct the original field element. -/
theorem stepForward_div_mod (v : Goldilocks) (base : Nat) :
    v = Goldilocks.ofNat (v.val % base) +ₚ
      (Goldilocks.ofNat (v.val / base) *ₚ Goldilocks.ofNat base) := by
  rw [← g_ofNat_mul, ← g_ofNat_add]
  apply Goldilocks.ext
  rw [Goldilocks.ofNat_val, Nat.mul_comm (v.val / base), Nat.mod_add_div,
    Nat.mod_eq_of_lt v.isLt]

/-- Three monotone skip bits encode the digit complementary to the remaining count. -/
theorem stepForward_wots_flags (v : Goldilocks) :
    let b := fun k => Goldilocks.ofNat (if k < 3 - v.val % 4 then 1 else 0)
    allZeroGoldilocks [stepBoolCheck (b 0), stepBoolCheck (b 1), stepBoolCheck (b 2),
      b 1 *ₚ Goldilocks.sub Goldilocks.one (b 0),
      b 2 *ₚ Goldilocks.sub Goldilocks.one (b 1),
      Goldilocks.sub v (Goldilocks.sub (Goldilocks.ofNat 3) ((b 0 +ₚ b 1) +ₚ b 2) +ₚ
        (Goldilocks.ofNat (v.val / 4) *ₚ Goldilocks.ofNat 4))] = true := by
  dsimp only
  have hr := stepForward_div_mod v 4
  have hm : v.val % 4 = 0 ∨ v.val % 4 = 1 ∨ v.val % 4 = 2 ∨ v.val % 4 = 3 := by omega
  rcases hm with hm | hm | hm | hm
  all_goals rw [hm] at hr ⊢
  all_goals change allZeroGoldilocks [Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
    Goldilocks.zero, Goldilocks.zero, Goldilocks.sub v _] = true
  all_goals simp only [allZeroGoldilocks, List.all_cons, List.all_nil,
    beq_self_eq_true, Bool.true_and, Bool.and_true, beq_iff_eq]
  all_goals exact g_sub_eq_zero_iff.mpr hr

/-- Cursor halving supplies both the direction bit and the parent index. -/
theorem stepForward_merkle_cursor (v : Goldilocks) :
    stepBoolCheck (Goldilocks.ofNat (v.val % 2)) = Goldilocks.zero ∧
    v = (Goldilocks.ofNat (v.val % 2) +ₚ Goldilocks.ofNat (v.val / 2)) +ₚ
      Goldilocks.ofNat (v.val / 2) := by
  constructor
  · have hm : v.val % 2 = 0 ∨ v.val % 2 = 1 := by omega
    rcases hm with hm | hm <;> rw [hm] <;> rfl
  · have hr := stepForward_div_mod v 2
    rw [← g_ofNat_add, ← g_ofNat_add]
    rw [← g_ofNat_mul, ← g_ofNat_add] at hr
    rw [show v.val % 2 + v.val / 2 + v.val / 2 = v.val % 2 + v.val / 2 * 2 by omega]
    exact hr

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_chain0_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (layer chain slot : Nat) :
    allZeroGoldilocks (stepOpGuardResiduals (.wotsChainStep0 slot)
      (Goldilocks.ofNat (layer * 2 ^ 44 + chain * 2 ^ 4))
      (stepOpRowInputs (pk, mu)
        (stepXmssSeedRow pk mu sig (.wotsChainStep0 layer chain slot) prev))) = true := by
  simp only [stepOpGuardResiduals, allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact stepForward_wots_flags (prev.getD (stRemPack + slot) Goldilocks.zero)
  all_goals step_forward_reduce

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_merkleA_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (layer lvl : Nat) :
    allZeroGoldilocks (stepOpGuardResiduals .xmssMerkleBlockA
      (Goldilocks.ofNat (layer * 2 ^ 48 + (lvl + 1) * 2 ^ 32))
      (stepOpRowInputs (pk, mu)
        (stepXmssSeedRow pk mu sig (.xmssMerkleBlockA layer lvl) prev))) = true := by
  simp only [stepOpGuardResiduals, stepMerkleBlockAGuards,
    allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h := stepForward_merkle_cursor (prev.getD stCursorIdx Goldilocks.zero)
    change allZeroGoldilocks [stepBoolCheck (Goldilocks.ofNat (_ % 2)),
      Goldilocks.sub (prev.getD stCursorIdx Goldilocks.zero)
        ((Goldilocks.ofNat (_ % 2) +ₚ Goldilocks.ofNat (_ / 2)) +ₚ Goldilocks.ofNat (_ / 2))] = true
    rw [h.1, ← h.2, g_sub_self]
    rfl
  all_goals step_forward_reduce

theorem stepForward_bit (n : Nat) :
    stepBoolCheck (Goldilocks.ofNat (n % 2)) = Goldilocks.zero := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_hmsg0_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) :
    allZeroGoldilocks (stepOpGuardResiduals .statefulHmsgBlock0 (Goldilocks.ofNat 0)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig .statefulHmsgBlock0 prev))) = true := by
  step_forward_reduce
  simp only [stepWeightedSum, List.range_succ, List.range_zero, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceLT, dite_true, Option.getD_some, stepXmssAux, ↓reduceIte,
    stepForward_bit, beq_self_eq_true, Bool.and_true, g_sub_self]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_pair_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (pair : Nat)
    (h : pair + 1 = 64 → ∀ j < 5, prev.getD (stRemPack + j) Goldilocks.zero = Goldilocks.zero) :
    allZeroGoldilocks (stepOpGuardResiduals (.wotsTellPairAbsorb (pair + 1 == 64))
      (Goldilocks.ofNat 0)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.wotsTellPairAbsorb pair) prev))) = true := by
  simp only [stepOpGuardResiduals, allZeroGoldilocks_append, Bool.and_eq_true]
  constructor
  · by_cases hp : pair + 1 = 64
    · simp only [hp, beq_self_eq_true, ↓reduceIte]
      apply (allZero_map_iff _ _).mpr
      exact h hp
    · have hb : (pair + 1 == 64) = false := by exact beq_eq_false_iff_ne.mpr hp
      rw [hb]
      rfl
  · step_forward_reduce

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_merkleTop_guards (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks)
    (hc : prev.getD stCursorIdx Goldilocks.zero = Goldilocks.zero)
    (hr : ∀ i < 4,
      (poseidon2Perm12 (stepXmssInput pk mu (.xmssMerkleBlockB true true) prev
        (stepXmssAux sig (.xmssMerkleBlockB true true) prev))).toList.getD i Goldilocks.zero =
        pk.pkRoot.toList.getD i Goldilocks.zero) :
    allZeroGoldilocks (stepOpGuardResiduals (.xmssMerkleBlockB true true) (Goldilocks.ofNat 0)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.xmssMerkleBlockB true true) prev))) = true := by
  simp only [stepOpGuardResiduals, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    allZeroGoldilocks_append, Bool.and_eq_true]
  refine ⟨?_, ?_, ?_⟩
  · step_forward_reduce
  · change allZeroGoldilocks [prev.getD stCursorIdx Goldilocks.zero] = true
    rw [hc]
    rfl
  · apply (allZero_map_iff _ _).mpr
    intro i hi
    apply g_sub_eq_zero_iff.mpr
    have hp := stepOp256_groupA_exact
      (stepXmssSeedRow pk mu sig (.xmssMerkleBlockB true true) prev)
      (stepOpHonestPermutationRow_groupA ..)
    change (stepOpPermTrace _).1.toList.getD i Goldilocks.zero = _
    rw [hp]
    exact hr i hi

/-- The randomizer is retained exactly by construction, without an acceptance premise. -/
theorem stepXmssRows_randomizer (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) :
    (stepXmssSig (stepOpSlotRow .xmssPoseidon2 (stepXmssRows pk mu sig) 0)).rRand = sig.rRand := by
  rfl

/-- Instruction classes used by the XMSS program. -/
def stepXmssSupported : StepOp → Bool
  | .idle | .statefulHmsgBlock0 | .statefulHmsgBlock1 | .statefulHmsgSqueeze
  | .hmsgDecompLimb _ | .wotsTellInit _ | .wotsChainStep0 _ _ _
  | .wotsChainStep1 _ _ | .wotsChainStep2 _ _ _ | .wotsTellPairAbsorb _
  | .wotsTellFinalSqueeze | .xmssMerkleBlockA _ _
  | .xmssMerkleBlockB false _ | .xmssMerkleBlockB true true => true
  | _ => false

theorem stepXmssProgram_supported :
    (buildSignerProgram .xmssPoseidon2).all stepXmssSupported = true := by
  decide +kernel

/-- Arithmetic and terminal checks left after supplying the honest local cells. -/
def StepXmssChecks (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (op : StepOp) (prev : List Goldilocks) : Prop :=
  match op with
  | .hmsgDecompLimb l =>
    (prev.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63 ∧
    (l = 4 → stepHmsgDecompExpected
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev)) l stAccOrU1 =
        Goldilocks.ofNat 192)
  | .wotsTellPairAbsorb pair =>
    pair + 1 = 64 → ∀ j < 5, prev.getD (stRemPack + j) Goldilocks.zero = Goldilocks.zero
  | .xmssMerkleBlockB true true =>
    prev.getD stCursorIdx Goldilocks.zero = Goldilocks.zero ∧
    ∀ i < 4, (poseidon2Perm12 (stepXmssInput pk mu op prev (stepXmssAux sig op prev))).toList.getD
      i Goldilocks.zero = pk.pkRoot.toList.getD i Goldilocks.zero
  | _ => True

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepXmss_seed_guards_of_checks (pk : AggValidatorPk) (mu : Digest5)
    (sig : AggNativeSignature) (op : StepOp) (prev : List Goldilocks)
    (hs : stepXmssSupported op = true) (hc : StepXmssChecks pk mu sig op prev) :
    allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev))) = true := by
  cases op <;> simp only [stepXmssSupported] at hs
  all_goals try contradiction
  case idle => exact stepXmss_plain_guards pk mu sig .idle prev True.intro
  case statefulHmsgBlock0 => exact stepXmss_hmsg0_guards pk mu sig prev
  case statefulHmsgBlock1 => exact stepXmss_plain_guards pk mu sig .statefulHmsgBlock1 prev True.intro
  case statefulHmsgSqueeze => exact stepXmss_plain_guards pk mu sig .statefulHmsgSqueeze prev True.intro
  case hmsgDecompLimb l => exact stepXmss_decomp_guards pk mu sig prev l hc.1 hc.2
  case wotsTellInit l => exact stepXmss_plain_guards pk mu sig (.wotsTellInit l) prev True.intro
  case wotsChainStep0 l c slot => exact stepXmss_chain0_guards pk mu sig prev l c slot
  case wotsChainStep1 l c => exact stepXmss_plain_guards pk mu sig (.wotsChainStep1 l c) prev True.intro
  case wotsChainStep2 l c odd => exact stepXmss_plain_guards pk mu sig (.wotsChainStep2 l c odd) prev True.intro
  case wotsTellPairAbsorb pair => exact stepXmss_pair_guards pk mu sig prev pair hc
  case wotsTellFinalSqueeze => exact stepXmss_plain_guards pk mu sig .wotsTellFinalSqueeze prev True.intro
  case xmssMerkleBlockA l lvl => exact stepXmss_merkleA_guards pk mu sig prev l lvl
  case xmssMerkleBlockB a b =>
    cases a with
    | false => exact stepXmss_plain_guards pk mu sig (.xmssMerkleBlockB false b) prev True.intro
    | true =>
      cases b with
      | false => contradiction
      | true => exact stepXmss_merkleTop_guards pk mu sig prev hc.1 hc.2


/-- A full active table follows from the remaining execution-wide checks.
    This statement uses the original checker, not a replacement acceptance predicate. -/
theorem stepXmssRows_table_of_checks (pk : AggValidatorPk) (mu : Digest5)
    (sig : AggNativeSignature)
    (hc : ∀ (i : Nat) row, (stepXmssRows pk mu sig)[i]? = some row →
      StepXmssChecks pk mu sig ((buildSignerProgram .xmssPoseidon2).getD i .idle) row.prevState) :
    stepOp256TableOk .xmssPoseidon2 [some (pk, mu)] (stepXmssRows pk mu sig) = true := by
  apply (stepXmssRows_table_iff pk mu sig).mpr
  intro i row hr
  obtain ⟨op, state, hop, he⟩ := stepForwardRun_at (pk, mu) (stepXmssCells pk mu sig)
    (buildSignerProgram .xmssPoseidon2) stepForwardZero i row hr
  have hs := List.all_eq_true.mp stepXmssProgram_supported op (List.mem_of_getElem? hop)
  have hopD : (buildSignerProgram .xmssPoseidon2).getD i .idle = op := by
    rw [List.getD_eq_getElem?_getD, hop]; rfl
  have hchecks := hc i row hr
  rw [hopD, he] at hchecks
  have hg := stepXmss_seed_guards_of_checks pk mu sig op state hs hchecks
  rw [hopD, he]
  change allZeroGoldilocks (stepOpGuardResiduals _ _
    (stepOpRowInputs (pk, mu) (populateStepOpNext _ _ _ (stepXmssSeedRow pk mu sig op state)))) = true
  rw [populateStepOpNext_inputs, stepOpGuardResiduals_congr_next]
  exact hg

/-- The constructed XMSS trace, indexed within its signer block. -/
def stepXmssR (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature) : Nat → StepOpRow :=
  stepOpSlotRow .xmssPoseidon2 (stepXmssRows pk mu sig) 0

theorem stepXmssR_at (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t : Nat) (ht : t < 512) :
    (stepXmssRows pk mu sig)[t]? = some (stepXmssR pk mu sig t) := by
  have hlt : t < (stepXmssRows pk mu sig).length := by rw [stepXmssRows_length]; exact ht
  simp only [stepXmssR, stepOpSlotRow, Nat.zero_mul, Nat.zero_add,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]

theorem stepXmssR_built (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t : Nat) (ht : t < 512) :
    stepXmssR pk mu sig t = stepForwardRow (pk, mu)
      ((buildSignerProgram .xmssPoseidon2).getD t .idle)
      (stepXmssR pk mu sig t).prevState
      (stepXmssCells pk mu sig ((buildSignerProgram .xmssPoseidon2).getD t .idle)
        (stepXmssR pk mu sig t).prevState) := by
  obtain ⟨op, state, hop, he⟩ := stepForwardRun_at (pk, mu) (stepXmssCells pk mu sig)
    (buildSignerProgram .xmssPoseidon2) stepForwardZero t _ (stepXmssR_at pk mu sig t ht)
  rw [List.getD_eq_getElem?_getD, hop, Option.getD_some, he]
  rfl

theorem stepXmssR_sem (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t : Nat) (op : StepOp) (ht : t + 1 < 512)
    (hop : (buildSignerProgram .xmssPoseidon2).getD t .idle = op)
    (hc : StepXmssChecks pk mu sig op (stepXmssR pk mu sig t).prevState) :
    StepRowSem (pk, mu) (stepXmssR pk mu sig) op t := by
  have hb := stepXmssR_built pk mu sig t (by omega)
  rw [hop] at hb
  have hgA := stepXmssRows_groupA pk mu sig _ (List.mem_of_getElem? (stepXmssR_at pk mu sig t (by omega)))
  have hvalid := (buildSignerProgram_kind_mem_and_valid .xmssPoseidon2 t).2
  rw [hop] at hvalid
  have hsup : stepXmssSupported op = true := by
    have hlen : t < (buildSignerProgram .xmssPoseidon2).length := by
      rw [buildSignerProgram_length.2.2.1]; omega
    have he : (buildSignerProgram .xmssPoseidon2)[t] = op := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some] using hop
    exact List.all_eq_true.mp stepXmssProgram_supported op (he ▸ List.getElem_mem hlen)
  have hg := stepXmss_seed_guards_of_checks pk mu sig op _ hsup hc
  have hcon : allZeroGoldilocks (stepOpConstraints (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs (pk, mu) (stepXmssR pk mu sig t))) = true := by
    rw [hb]
    exact (stepForwardRow_constraints_iff _ _ _ _ hvalid).mpr hg
  have hparts := (stepOpConstraints_iff_guard_and_next _ _ _ hvalid).mp hcon
  refine ⟨stepOp256_groupA_exact _ hgA, hparts.1, ?_⟩
  intro j hj
  have hshift := stepForwardRun_shift (pk, mu) (stepXmssCells pk mu sig)
    (buildSignerProgram .xmssPoseidon2) stepForwardZero t _ _
    (stepXmssR_at pk mu sig t (by omega)) (stepXmssR_at pk mu sig (t + 1) ht)
  unfold stepPrev
  rw [← hshift]
  exact hparts.2 j hj

/-- Native acceptance gives one bounded leaf and one layer verifying to the public root. -/
theorem stepXmssNative_layer (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    ∃ ls : WotsLayerSig, sig.layers = [ls] ∧ sig.statefulLeafIdx < 64 ∧
      verifyWotsLayer xmssPoseidon2Geom pk 0 0 sig.statefulLeafIdx
        (computeHmsgStateful pk sig.rRand (computeMessageMu pk msg) sig.statefulLeafIdx ls.tswCtr)
        ls = some pk.pkRoot := by
  unfold verifyAggNativeSig at h
  split at h
  · contradiction
  · rename_i hc
    have hfalse := Bool.eq_false_iff.mpr hc
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hfalse
    have hlen : sig.layers.length = 1 := hfalse.2
    cases hl : sig.layers with
    | nil => simp [hl] at hlen
    | cons ls tail =>
      have ht : tail = [] := by
        have htail : tail.length = 0 := by
          have hh := hlen
          rw [hl, List.length_cons] at hh
          omega
        exact List.eq_nil_of_length_eq_zero htail
      subst tail
      simp only [hl] at h
      change verifyAggNativeSigStateful xmssPoseidon2Geom pk (computeMessageMu pk msg) sig ls [] = true at h
      unfold verifyAggNativeSigStateful at h
      split at h
      · contradiction
      · rename_i hc'
        have hf := Bool.eq_false_iff.mpr hc'
        simp only [Bool.or_eq_false_iff] at hf
        have hleaf : sig.statefulLeafIdx < 64 := by
          have hh := hf.2
          change (!decide (sig.statefulLeafIdx < 64)) = false at hh
          by_cases hb : sig.statefulLeafIdx < 64
          · exact hb
          · simp [hb] at hh
        have hd : sig.statefulLeafIdx / 64 = 0 := Nat.div_eq_of_lt hleaf
        have hm : sig.statefulLeafIdx % 64 = sig.statefulLeafIdx := Nat.mod_eq_of_lt hleaf
        change (match verifyWotsLayer xmssPoseidon2Geom pk 0 (sig.statefulLeafIdx / 64)
          (sig.statefulLeafIdx % 64)
          (computeHmsgStateful pk sig.rRand (computeMessageMu pk msg)
            (sig.statefulLeafIdx % 64) ls.tswCtr) ls with
          | none => false
          | some root => root == pk.pkRoot) = true at h
        rw [hd, hm] at h
        split at h
        · contradiction
        · rename_i root hr
          have he : root = pk.pkRoot := beq_iff_eq.mp h
          exact ⟨ls, rfl, hleaf, he ▸ hr⟩


/-- Reconstruction without invoking the classical modular-arithmetic lemmas. -/
theorem stepForwardWeighted_digits (B w : Nat) (f : Nat → Goldilocks)
    (hB : B ≤ goldilocksPrime) (hB0 : 0 < B) :
    ∀ n, (∀ i < n, f i = Goldilocks.ofNat ((w / B ^ i) % B)) →
      stepWeightedNat f (fun i => B ^ i) n + B ^ n * (w / B ^ n) = w
  | 0, _ => by
    rw [Nat.pow_zero, Nat.div_one, Nat.one_mul]
    exact Nat.zero_add w
  | n + 1, h => by
    have ih := stepForwardWeighted_digits B w f hB hB0 n (fun i hi => h i (by omega))
    have hd : (w / B ^ n) % B < goldilocksPrime :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ hB0) hB
    have hq := Nat.div_add_mod (w / B ^ n) B
    have key : w / B ^ n % B * B ^ n + B ^ n * B * (w / B ^ n / B) = B ^ n * (w / B ^ n) := by
      rw [Nat.mul_comm (w / B ^ n % B) (B ^ n), Nat.mul_assoc, ← Nat.mul_add, Nat.add_comm, hq]
    rw [stepWeightedNat_succ, h n (by omega), Goldilocks.ofNat_val, Nat.mod_eq_of_lt hd,
      Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_assoc, key]
    exact ih

theorem stepForwardWeighted_bits (w n : Nat) (f : Nat → Goldilocks)
    (hf : ∀ i < n, f i = Goldilocks.ofNat ((w / 2 ^ i) % 2)) :
    stepWeightedSum f (fun i => 2 ^ i) n = Goldilocks.ofNat (w % 2 ^ n) := by
  have he := stepForwardWeighted_digits 2 w f (by decide) (by decide) n hf
  have hb : stepWeightedNat f (fun i => 2 ^ i) n < 2 ^ n :=
    stepWeightedNat_bits_lt f n (fun i hi => by
      rw [hf i hi]
      have hm : w / 2 ^ i % 2 = 0 ∨ w / 2 ^ i % 2 = 1 := by omega
      rcases hm with hm | hm
      · exact Or.inl (by rw [hm]; rfl)
      · exact Or.inr (by rw [hm]; rfl))
  have hdiv := Nat.mod_add_div w (2 ^ n)
  rw [stepWeightedSum_eq_ofNat]
  congr 1
  omega

theorem stepXmssR_aux (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t i : Nat) (ht : t < 512) (hi : i < 38) (op : StepOp)
    (hop : (buildSignerProgram .xmssPoseidon2).getD t .idle = op) :
    stepAux (stepXmssR pk mu sig) t i =
      stepXmssAux sig op (stepXmssR pk mu sig t).prevState i := by
  have he := congrArg (fun r : StepOpRow => r.aux.getD i Goldilocks.zero)
    (stepXmssR_built pk mu sig t ht)
  rw [hop] at he
  exact he.trans (stepXmssSeedRow_aux pk mu sig op _ i hi)

/-- The first three interpreter instructions compute precisely native stateful Hmsg. -/
theorem stepXmssR_hmsg (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (hleaf : sig.statefulLeafIdx < 64) :
    stepHmsgOf (stepRegsAt (stepXmssR pk mu sig) 3).main =
      computeHmsgStateful pk sig.rRand mu sig.statefulLeafIdx ls.tswCtr ∧
    (∀ s < 6, (stepRegsAt (stepXmssR pk mu sig) 3).rem.get s = Goldilocks.zero) ∧
    (stepRegsAt (stepXmssR pk mu sig) 3).acc = Goldilocks.zero ∧
    StepAddrOk (stepRegsAt (stepXmssR pk mu sig) 3) sig.statefulLeafIdx 0 := by
  let R := stepXmssR pk mu sig
  have h0 := stepXmssR_sem pk mu sig 0 .statefulHmsgBlock0 (by decide) rfl True.intro
  have h1 := stepXmssR_sem pk mu sig 1 .statefulHmsgBlock1 (by decide) rfl True.intro
  have h2 := stepXmssR_sem pk mu sig 2 .statefulHmsgSqueeze (by decide) rfl True.intro
  obtain ⟨_, _, hin0, hr1⟩ := stepSem_statefulHmsgBlock0 h0
  obtain ⟨hin1, hr2⟩ := stepSem_statefulHmsgBlock1 h1
  obtain ⟨hin2, hr3⟩ := stepSem_statefulHmsgSqueeze h2
  have hb6 : stepWeightedSum (stepAux R 0) (fun i => 2 ^ i) 6 = Goldilocks.ofNat sig.statefulLeafIdx := by
    have hh := stepForwardWeighted_bits sig.statefulLeafIdx 6 (stepAux R 0) (fun i hi => by
      rw [stepXmssR_aux pk mu sig 0 i (by decide) (by omega) .statefulHmsgBlock0 rfl]
      simp only [stepXmssAux, hi, ↓reduceIte])
    simpa only [Nat.mod_eq_of_lt hleaf] using hh
  have hb32 : stepWeightedSum (fun i => stepAux R 0 (6 + i)) (fun i => 2 ^ i) 32 =
      Goldilocks.ofNat (ls.tswCtr % 2 ^ 32) := by
    apply stepForwardWeighted_bits
    intro i hi
    rw [stepXmssR_aux pk mu sig 0 (6 + i) (by decide) (by omega) .statefulHmsgBlock0 rfl]
    simp only [stepXmssAux, hlayers, List.getD_cons_zero,
      show ¬6 + i < 6 by omega, show 6 + i < 38 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  have hin0' : (R 0).stIn = hmsgStatefulIn0 pk mu sig.statefulLeafIdx ls.tswCtr := by
    rw [hin0, hb6, hb32]
    unfold hmsgStatefulIn0
    rw [Nat.mod_eq_of_lt (show sig.statefulLeafIdx < 2 ^ 32 by omega), g_ofNat_add, g_ofNat_mul]
  have hrand : stepAuxLane R 1 0 = sig.rRand := by rfl
  have main1 : (stepRegsAt R 1).main = poseidon2Perm12 (hmsgStatefulIn0 pk mu sig.statefulLeafIdx ls.tswCtr) := by
    rw [hr1]
    change poseidon2Perm12 (R 0).stIn = _
    rw [hin0']
  have hin1' : (R 1).stIn = hmsgStatefulIn1
      (poseidon2Perm12 (hmsgStatefulIn0 pk mu sig.statefulLeafIdx ls.tswCtr)) sig.rRand mu := by
    rw [hin1, main1, hrand]
    rfl
  have main2 : (stepRegsAt R 2).main = poseidon2Perm12 (R 1).stIn := by rw [hr2]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr3]
    change stepHmsgOf (poseidon2Perm12 (R 2).stIn) = _
    rw [hin2]
    unfold stepSqueezeIn
    rw [main2, hin1', computeHmsgStateful_eq_states]
    rfl
  · intro s hs
    rw [hr3]
    rcases s with _ | _ | _ | _ | _ | _ | s <;> first | rfl | omega
  · rw [hr3]
  · constructor
    · rw [hr3, hr2, hr1]
      exact hb6
    · rw [hr3, hr2, hr1]
      rfl
    · rw [hr3, hr2, hr1]
      rfl


/-- The native layer checks the canonical digest digits and their target sum. -/
theorem stepXmssNative_digits (pk : AggValidatorPk) (d : Digest5) (ls : WotsLayerSig)
    (leaf : Nat) (h : verifyWotsLayer xmssPoseidon2Geom pk 0 0 leaf d ls = some pk.pkRoot) :
    checkDigest5Limbs63 d = true ∧
    listNatSum ((List.range' 0 128).map (stepDigit d)) = 192 ∧
    ls.wotsChains.length = 128 ∧ ls.merklePath.length = 6 := by
  unfold verifyWotsLayer at h
  split at h
  · rename_i hlen
    simp only [Bool.and_eq_true, beq_iff_eq] at hlen
    cases he : extractWotsDigitsChecked xmssPoseidon2Geom d with
    | none => simp [he] at h
    | some ds =>
      simp only [he] at h
      split at h
      · rename_i hsum
        have hchk : checkDigest5Limbs63 d = true := by
          unfold extractWotsDigitsChecked at he
          split at he
          · assumption
          · contradiction
        have hd := stepDigits_extract xmssPoseidon2Geom d rfl hchk
        rw [he] at hd
        have hd' : ds = (List.range' 0 128).map (stepDigit d) := Option.some.inj hd
        have hsum' : listNatSum ds = 192 := beq_iff_eq.mp hsum
        exact ⟨hchk, hd' ▸ hsum', hlen.1, hlen.2⟩
      · contradiction
  · contradiction

theorem stepXmssProgram_decomp (l : Nat) (hl : l < 5) :
    (buildSignerProgram .xmssPoseidon2).getD (3 + l) .idle = .hmsgDecompLimb l := by
  rcases l with _ | _ | _ | _ | _ | l <;> first | rfl | omega

/-- A digest range check bounds each decomposition source register. -/
theorem stepForward_digest_limb (prev : List Goldilocks) (l : Nat) (hl : l < 5)
    (h : checkDigest5Limbs63 (stepHmsgOf (stepRegs (fun j => prev.getD j Goldilocks.zero)).main) = true) :
    (prev.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63 := by
  simp only [checkDigest5Limbs63, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases l with _ | _ | _ | _ | _ | l
  · exact h.1.1.1.1
  · exact h.1.1.1.2
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2
  · omega

/-- The computed accumulator adds exactly this limb's native digits, independently of guards. -/
theorem stepXmss_decomp_acc_expected (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (prev : List Goldilocks) (l : Nat) (hl : l < 5) :
    stepHmsgDecompExpected (stepOpRowInputs (pk, mu)
      (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev)) l stAccOrU1 =
    prev.getD stAccOrU1 Goldilocks.zero +ₚ Goldilocks.ofNat
      (listNatSum ((List.range' (31 * l) (stepLimbDigits l)).map
        (stepDigit (stepHmsgOf (stepRegs (fun j => prev.getD j Goldilocks.zero)).main)))) := by
  let x := stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig (.hmsgDecompLimb l) prev)
  let d := stepHmsgOf (stepRegs (fun j => prev.getD j Goldilocks.zero)).main
  have hlimb : digest5Limb d l = prev.getD (stMainSponge + l) Goldilocks.zero := by
    rcases l with _ | _ | _ | _ | _ | l <;> first | rfl | omega
  have hn : stepLimbDigits l ≤ 31 := by unfold stepLimbDigits; split <;> omega
  have hd : ∀ i ∈ List.range (stepLimbDigits l), x.aux i = Goldilocks.ofNat (stepDigit d (31 * l + i)) := by
    intro i hi
    have hi' := List.mem_range.mp hi
    have hi31 : i < 31 := by omega
    rw [stepXmssSeedRow_aux pk mu sig _ prev i (by omega)]
    simp only [stepXmssAux, hi31, ↓reduceIte]
    unfold stepDigit
    rw [show (31 * l + i) / 31 = l by omega, show (31 * l + i) % 31 = i by omega, hlimb]
  have he := stepPlainSum_field x (stepDigit d) l (List.range (stepLimbDigits l)) 0 hd
  change x.prev stAccOrU1 +ₚ stepPlainSum x.aux (stepLimbDigits l) = _
  unfold stepPlainSum
  have hz : Goldilocks.ofNat 0 = Goldilocks.zero := rfl
  rw [hz] at he
  rw [he, Nat.zero_add, range'_eq_map, List.map_map]
  rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- Native digit checks establish the full five-row decomposition segment. -/
theorem stepXmssR_decomp (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (hchk : checkDigest5Limbs63 (stepHmsgOf (stepRegsAt (stepXmssR pk mu sig) 3).main) = true)
    (hsum : listNatSum ((List.range' 0 128).map
      (stepDigit (stepHmsgOf (stepRegsAt (stepXmssR pk mu sig) 3).main))) = 192)
    (hacc : (stepRegsAt (stepXmssR pk mu sig) 3).acc = Goldilocks.zero) :
    StepRunAt (pk, mu) (stepXmssR pk mu sig) ((List.range 5).map StepOp.hmsgDecompLimb) 3 := by
  let R := stepXmssR pk mu sig
  let d := stepHmsgOf (stepRegsAt R 3).main
  have hp : ∀ l, l ≤ 4 →
      (stepRegsAt R (3 + l)).main = (stepRegsAt R 3).main ∧
      (stepRegsAt R (3 + l)).acc = Goldilocks.ofNat
        (listNatSum ((List.range' 0 (31 * l)).map (stepDigit d))) ∧
      ∀ j < l, StepRowSem (pk, mu) R (.hmsgDecompLimb j) (3 + j) := by
    intro l
    induction l with
    | zero =>
      intro _
      exact ⟨rfl, hacc, fun j hj => False.elim (by omega)⟩
    | succ l ih =>
      intro hl
      obtain ⟨hm, ha, hrun⟩ := ih (by omega)
      have hlt : ((R (3 + l)).prevState.getD (stMainSponge + l) Goldilocks.zero).val < 2 ^ 63 := by
        apply stepForward_digest_limb _ l (by omega)
        change checkDigest5Limbs63 (stepHmsgOf (stepRegsAt R (3 + l)).main) = true
        rw [hm]
        exact hchk
      have hsem := stepXmssR_sem pk mu sig (3 + l) (.hmsgDecompLimb l) (by omega)
        (stepXmssProgram_decomp l (by omega)) ⟨hlt, fun he => False.elim (by omega)⟩
      obtain ⟨_, _, hacc', _, hf⟩ := stepDecomp_row (by omega : l < 5) hsem
        (fun s => ((stepRegsAt R (3 + l)).rem.get s).val)
        (listNatSum ((List.range' 0 (31 * l)).map (stepDigit d)))
        (fun s _ => (g_ofNat_self _).symm) ha
      have hn : stepLimbDigits l = 31 := by simp [stepLimbDigits, show l < 4 by omega]
      rw [hm, hn] at hacc'
      refine ⟨?_, ?_, ?_⟩
      · have he : 3 + (l + 1) = 3 + l + 1 := by omega
        rw [he, hf]
        exact hm
      · have he : 3 + (l + 1) = 3 + l + 1 := by omega
        rw [he, hacc']
        apply congrArg Goldilocks.ofNat
        rw [show 31 * (l + 1) = 31 * l + 31 by omega,
          range'_split, Nat.zero_add, List.map_append, listNatSum_append]
      · intro j hj
        by_cases he : j = l
        · subst j; exact hsem
        · exact hrun j (by omega)
  obtain ⟨hm4, ha4, hrun4⟩ := hp 4 (by decide)
  have hlt4 : ((R 7).prevState.getD (stMainSponge + 4) Goldilocks.zero).val < 2 ^ 63 := by
    apply stepForward_digest_limb _ 4 (by decide)
    change checkDigest5Limbs63 (stepHmsgOf (stepRegsAt R 7).main) = true
    rw [hm4]
    exact hchk
  have he4 : stepHmsgDecompExpected (stepOpRowInputs (pk, mu)
      (stepXmssSeedRow pk mu sig (.hmsgDecompLimb 4) (R 7).prevState)) 4 stAccOrU1 = Goldilocks.ofNat 192 := by
    rw [stepXmss_decomp_acc_expected pk mu sig _ 4 (by decide)]
    change (stepRegsAt R 7).acc +ₚ Goldilocks.ofNat
      (listNatSum ((List.range' 124 4).map (stepDigit (stepHmsgOf (stepRegsAt R 7).main)))) = _
    rw [ha4, hm4, ← g_ofNat_add]
    have he : List.range' 0 128 = List.range' 0 124 ++ List.range' 124 4 := by
      exact range'_split 124 0 4
    rw [he, List.map_append, listNatSum_append] at hsum
    exact congrArg Goldilocks.ofNat hsum
  have hsem4 := stepXmssR_sem pk mu sig 7 (.hmsgDecompLimb 4) (by decide) rfl ⟨hlt4, fun _ => he4⟩
  intro i hi
  have hi5 : i < 5 := by simpa only [List.length_map, List.length_range] using hi
  simp only [List.getElem_map, List.getElem_range]
  by_cases he : i = 4
  · subst i; exact hsem4
  · exact hrun4 i (by omega)


/-- Natural-number model of the remaining-count registers after consuming `c` chains. -/
def stepForwardRemNat (v : Nat → Nat) : Nat → Nat → Nat
  | 0, s => v s
  | c + 1, s => if s = wotsPackSlot c then stepForwardRemNat v c s / 4 else stepForwardRemNat v c s

theorem stepForwardRemNat_le (v : Nat → Nat) (c s : Nat) : stepForwardRemNat v c s ≤ v s := by
  induction c with
  | zero => exact Nat.le_refl _
  | succ c ih =>
    unfold stepForwardRemNat
    split
    · exact Nat.le_trans (Nat.div_le_self _ _) ih
    · exact ih

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem stepForwardRemNat_end (v : Nat → Nat)
    (hv : ∀ s < 5, v s < 4 ^ (if s < 3 then 26 else 25)) :
    ∀ s < 5, stepForwardRemNat v 128 s = 0 := by
  intro s hs
  have hbound := hv s hs
  rcases s with _ | _ | _ | _ | _ | s
  all_goals first | omega | skip
  all_goals simp only [stepForwardRemNat, wotsPackSlot, Nat.reduceLT, Nat.reduceEqDiff,
    ↓reduceIte, Nat.div_div_eq_div_mul]
  all_goals exact Nat.div_eq_of_lt hbound

theorem stepForwardRegs_rem (prev : List Goldilocks) (s : Nat) (hs : s < 6) :
    (stepRegs (fun j => prev.getD j Goldilocks.zero)).rem.get s =
      prev.getD (stRemPack + s) Goldilocks.zero := by
  rcases s with _ | _ | _ | _ | _ | _ | s <;> first | rfl | omega

/-- Exact schedule of one seven-row WOTS pair. -/
theorem stepXmssProgram_pairs : ∀ p < 64,
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p) .idle =
      .wotsChainStep0 0 (2 * p) (wotsPackSlot (2 * p)) ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 1) .idle = .wotsChainStep1 0 (2 * p) ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 2) .idle = .wotsChainStep2 0 (2 * p) false ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 3) .idle =
      .wotsChainStep0 0 (2 * p + 1) (wotsPackSlot (2 * p + 1)) ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 4) .idle = .wotsChainStep1 0 (2 * p + 1) ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 5) .idle = .wotsChainStep2 0 (2 * p + 1) true ∧
    (buildSignerProgram .xmssPoseidon2).getD (9 + 7 * p + 6) .idle = .wotsTellPairAbsorb p := by
  decide +kernel

/-- One constructed chain consumes precisely one base-4 quotient, without needing its digit invariant. -/
theorem stepXmssR_chain_rem (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (t c : Nat) (odd : Bool) (ht : t + 3 < 512)
    (h0 : (buildSignerProgram .xmssPoseidon2).getD t .idle = .wotsChainStep0 0 c (wotsPackSlot c))
    (h1 : (buildSignerProgram .xmssPoseidon2).getD (t + 1) .idle = .wotsChainStep1 0 c)
    (h2 : (buildSignerProgram .xmssPoseidon2).getD (t + 2) .idle = .wotsChainStep2 0 c odd) :
    (stepRegsAt (stepXmssR pk mu sig) (t + 3)).rem =
      (stepRegsAt (stepXmssR pk mu sig) t).rem.set (wotsPackSlot c)
        (Goldilocks.ofNat (((stepRegsAt (stepXmssR pk mu sig) t).rem.get (wotsPackSlot c)).val / 4)) := by
  let R := stepXmssR pk mu sig
  have hs : wotsPackSlot c < 6 := Nat.lt_succ_of_lt (wotsPackSlot_lt_5 c)
  have hsem0 := stepXmssR_sem pk mu sig t _ (by omega) h0 True.intro
  have hsem1 := stepXmssR_sem pk mu sig (t + 1) _ (by omega) h1 True.intro
  have hsem2 := stepXmssR_sem pk mu sig (t + 2) _ (by omega) h2 (by cases odd <;> exact True.intro)
  have hr1 := (stepSem_wotsChainStep0 hs hsem0).2.2.2.2.2.2.2
  have hr2 : stepRegsAt R (t + 2) = _ := (stepSem_wotsChainStep1 hsem1).2
  have hr3 : (stepRegsAt R (t + 3)).rem = (stepRegsAt R (t + 2)).rem := by
    cases odd
    · have he : stepRegsAt R (t + 3) = _ := (stepSem_wotsChainStep2_even hsem2).2
      rw [he]
    · have he : stepRegsAt R (t + 3) = _ := (stepSem_wotsChainStep2_odd hsem2).2
      rw [he]
  rw [hr3, hr2, hr1]
  have ha := stepXmssR_aux pk mu sig t 7 (by omega) (by decide) _ h0
  change stepAux R t 7 = _ at ha
  rw [ha]
  change (stepRegsAt R t).rem.set (wotsPackSlot c)
      (Goldilocks.ofNat (((R t).prevState.getD (stRemPack + wotsPackSlot c) Goldilocks.zero).val / 4)) = _
  have hget : (stepRegsAt R t).rem.get (wotsPackSlot c) =
      (R t).prevState.getD (stRemPack + wotsPackSlot c) Goldilocks.zero :=
    stepForwardRegs_rem _ _ hs
  rw [hget]

/-- Updating a quotient register agrees with the natural-number consumption model. -/
theorem stepForwardRemNat_step (v : Nat → Nat) (r : StepRem) (c : Nat)
    (hr : ∀ s < 5, r.get s = Goldilocks.ofNat (stepForwardRemNat v c s))
    (hv : ∀ s < 5, v s < goldilocksPrime) :
    ∀ s < 5, (r.set (wotsPackSlot c) (Goldilocks.ofNat ((r.get (wotsPackSlot c)).val / 4))).get s =
      Goldilocks.ofNat (stepForwardRemNat v (c + 1) s) := by
  intro s hs
  rw [StepRem.get_set _ _ _ _ (Nat.lt_succ_of_lt (wotsPackSlot_lt_5 c))]
  unfold stepForwardRemNat
  by_cases he : s = wotsPackSlot c
  · rw [ite_eq_left he, ite_eq_left he, ← he, hr s hs, Goldilocks.ofNat_val,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (stepForwardRemNat_le v c s) (hv s hs))]
  · rw [ite_eq_right he, ite_eq_right he]
    exact hr s hs


/-- Packed native remaining counts fit the five register capacities. -/
theorem stepForward_pack_bounds (d : Digest5) (r : StepRem)
    (hpack : ∀ s < 6, r.get s = Goldilocks.ofNat
      (stepPackFold (stepDigit d) s (List.range' 0 128) 0)) :
    ∀ s < 5, (r.get s).val < 4 ^ (if s < 3 then 26 else 25) := by
  intro s hs
  rcases s with _ | _ | _ | _ | _ | s
  · have he := hpack 0 (by decide)
    rw [stepPackFold_slot _ 0 0 26 (by decide +kernel) (by decide) rfl] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 0 26).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 26 < goldilocksPrime))]
    exact hb
  · have he := hpack 1 (by decide)
    rw [stepPackFold_slot _ 1 26 26 (by decide +kernel) (by decide) rfl] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 26 26).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 26 < goldilocksPrime))]
    exact hb
  · have he := hpack 2 (by decide)
    rw [stepPackFold_slot _ 2 52 26 (by decide +kernel) (by decide) rfl] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 52 26).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 26 < goldilocksPrime))]
    exact hb
  · have he := hpack 3 (by decide)
    rw [stepPackFold_slot _ 3 78 25 (by decide +kernel) (by decide) rfl] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 78 25).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 25 < goldilocksPrime))]
    exact hb
  · have he := hpack 4 (by decide)
    rw [stepPackFold_slot _ 4 103 25 (by decide +kernel) (by decide) rfl] at he
    have hb := evalBaseDigits_lt_pow 4 (by decide)
      ((List.range' 103 25).map (fun c => 3 - stepDigit d c)) (fun x hx => by
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
        omega)
    rw [List.length_map, List.length_range'] at hb
    rw [he, Goldilocks.ofNat_val, Nat.mod_eq_of_lt
      (Nat.lt_trans hb (by decide : 4 ^ 25 < goldilocksPrime))]
    exact hb
  · omega

/-- Glue verified instruction segments without assuming a valid table. -/
theorem stepForwardRunAt_append (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (a b : List StepOp) (t : Nat) (ha : StepRunAt pub R a t)
    (hb : StepRunAt pub R b (t + a.length)) : StepRunAt pub R (a ++ b) t := by
  intro i hi
  by_cases hia : i < a.length
  · rw [List.getElem_append_left hia]
    exact ha i hia
  · have hib : i - a.length < b.length := by rw [List.length_append] at hi; omega
    rw [List.getElem_append_right (Nat.le_of_not_lt hia)]
    have he := hb (i - a.length) hib
    have ht : t + a.length + (i - a.length) = t + i := by omega
    rw [ht] at he
    exact he

theorem stepForwardRunAt_pairs (pub : AggValidatorPk × Digest5) (R : Nat → StepOpRow)
    (layer t n : Nat) (h : ∀ p < n, StepRunAt pub R (stepPairOps layer p) (t + 7 * p)) :
    StepRunAt pub R ((List.range n).flatMap (stepPairOps layer)) t := by
  induction n with
  | zero => intro i hi; simp at hi
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply stepForwardRunAt_append
    · exact ih (fun p hp => h p (by omega))
    · have hl : ((List.range n).flatMap (stepPairOps layer)).length = 7 * n :=
        by rw [flatMap_range_uniform_length _ 7 (fun _ => rfl)]; omega
      rw [hl]
      exact h n (by omega)

theorem stepXmssR_pair_run (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (p : Nat) (hp : p < 64)
    (hcheck : p + 1 = 64 → ∀ s < 5,
      (stepXmssR pk mu sig (9 + 7 * p + 6)).prevState.getD (stRemPack + s) Goldilocks.zero =
        Goldilocks.zero) :
    StepRunAt (pk, mu) (stepXmssR pk mu sig) (stepPairOps 0 p) (9 + 7 * p) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := stepXmssProgram_pairs p hp
  intro i hi
  change i < 7 at hi
  rcases i with _ | _ | _ | _ | _ | _ | _ | i
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h0 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h1 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h2 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h3 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h4 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h5 True.intro
  · exact stepXmssR_sem pk mu sig _ _ (by omega) h6 hcheck
  · exact False.elim (by omega)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- The constructed WOTS segment exhausts the packed counts and satisfies every row guard. -/
theorem stepXmssR_wots (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (hbound : ∀ s < 5, ((stepRegsAt (stepXmssR pk mu sig) 8).rem.get s).val <
      4 ^ (if s < 3 then 26 else 25)) :
    StepRunAt (pk, mu) (stepXmssR pk mu sig) (stepWotsOps 0) 8 := by
  let R := stepXmssR pk mu sig
  let v := fun s => ((stepRegsAt R 8).rem.get s).val
  have hv : ∀ s < 5, v s < goldilocksPrime := fun s _ => ((stepRegsAt R 8).rem.get s).isLt
  have hinit := stepXmssR_sem pk mu sig 8 (.wotsTellInit 0) (by decide) rfl True.intro
  have hr9 := (stepSem_wotsTellInit hinit).2
  have hpref : ∀ p, p ≤ 64 →
      (∀ s < 5, (stepRegsAt R (9 + 7 * p)).rem.get s = Goldilocks.ofNat (stepForwardRemNat v (2 * p) s)) ∧
      (∀ q < p, StepRunAt (pk, mu) R (stepPairOps 0 q) (9 + 7 * q)) := by
    intro p
    induction p with
    | zero =>
      intro _
      constructor
      · intro s _
        change (stepRegsAt R 9).rem.get s = Goldilocks.ofNat (v s)
        rw [hr9]
        exact (g_ofNat_self _).symm
      · intro q hq; exact False.elim (by omega)
    | succ p ih =>
      intro hp
      obtain ⟨hm, hrun⟩ := ih (by omega)
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := stepXmssProgram_pairs p (by omega)
      have he := stepXmssR_chain_rem pk mu sig (9 + 7 * p) (2 * p) false (by omega) h0 h1 h2
      have ho := stepXmssR_chain_rem pk mu sig (9 + 7 * p + 3) (2 * p + 1) true (by omega) h3
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using h4)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using h5)
      have hm3 : ∀ s < 5, (stepRegsAt R (9 + 7 * p + 3)).rem.get s =
          Goldilocks.ofNat (stepForwardRemNat v (2 * p + 1) s) := by
        intro s hs
        rw [he]
        exact stepForwardRemNat_step v _ (2 * p) hm hv s hs
      have hm6 : ∀ s < 5, (stepRegsAt R (9 + 7 * p + 6)).rem.get s =
          Goldilocks.ofNat (stepForwardRemNat v (2 * p + 2) s) := by
        intro s hs
        have ho' : (stepRegsAt R (9 + 7 * p + 6)).rem = _ := ho
        rw [ho']
        exact stepForwardRemNat_step v _ (2 * p + 1) hm3 hv s hs
      have hc : p + 1 = 64 → ∀ s < 5,
          (R (9 + 7 * p + 6)).prevState.getD (stRemPack + s) Goldilocks.zero = Goldilocks.zero := by
        intro hlast s hs
        have hget : (stepRegsAt R (9 + 7 * p + 6)).rem.get s =
            (R (9 + 7 * p + 6)).prevState.getD (stRemPack + s) Goldilocks.zero :=
          stepForwardRegs_rem _ _ (by omega)
        rw [← hget, hm6 s hs, show 2 * p + 2 = 128 by omega,
          stepForwardRemNat_end v hbound s hs]
        rfl
      have hpair := stepXmssR_pair_run pk mu sig p (by omega) hc
      have habs : StepRowSem (pk, mu) R (.wotsTellPairAbsorb p) (9 + 7 * p + 6) :=
        hpair 6 (by change 6 < 7; decide)
      have hnext : stepRegsAt R (9 + 7 * p + 7) = _ := (stepSem_wotsTellPairAbsorb habs).2.2
      constructor
      · intro s hs
        rw [show 9 + 7 * (p + 1) = 9 + 7 * p + 7 by omega, hnext]
        exact hm6 s hs
      · intro q hq
        by_cases heq : q = p
        · subst q; exact hpair
        · exact hrun q (by omega)
  have hpairs := (hpref 64 (by decide)).2
  have hsqueeze := stepXmssR_sem pk mu sig 457 .wotsTellFinalSqueeze (by decide) rfl True.intro
  unfold stepWotsOps
  apply stepForwardRunAt_append
  · apply stepForwardRunAt_append
    · intro i hi
      have hi0 : i = 0 := by change i < 1 at hi; omega
      subst i; exact hinit
    · exact stepForwardRunAt_pairs (pk, mu) R 0 9 64 hpairs
  · have hl : ([StepOp.wotsTellInit 0] ++ (List.range 64).flatMap (stepPairOps 0)).length = 449 := by
      rw [List.length_append, flatMap_range_uniform_length _ 7 (fun _ => rfl)]
      rfl
    rw [hl]
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i; exact hsqueeze


set_option maxHeartbeats 1000000 in
/-- Layer computation without assuming the final root-comparison guard. -/
theorem stepLayer_verify_forward {pub : AggValidatorPk × Digest5} {R : Nat → StepOpRow}
    {geom : AggSigGeometry} {layer h tD kpN tree ctr : Nat}
    (hDec : StepRunAt pub R ((List.range 5).map StepOp.hmsgDecompLimb) tD)
    (hWots : StepRunAt pub R (stepWotsOps layer) (tD + 5))
    (hRem0 : ∀ s < 6, (stepRegsAt R tD).rem.get s = Goldilocks.zero)
    (hAcc0 : (stepRegsAt R tD).acc = Goldilocks.zero)
    (hAddr : StepAddrOk (stepRegsAt R tD) kpN tree)
    (hA : ∀ l < h, StepRowSem pub R (.xmssMerkleBlockA layer l) (tD + 455 + 2 * l))
    (hBin : ∀ l < h, (R (tD + 455 + 2 * l + 1)).stIn =
      stepMerkleBIn (stepRegsAt R (tD + 455 + 2 * l + 1)))
    (hBnext : ∀ l, l + 1 < h → stepRegsAt R (tD + 455 + 2 * l + 2) =
      { stepRegsAt R (tD + 455 + 2 * l + 1) with
        work := (stepPermAt R (tD + 455 + 2 * l + 1)).b0 })
    (hLastCur : (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)).cursor = Goldilocks.zero)
    (hl : layer < 64) (hk : kpN < 2 ^ 28) (hh : 0 < h) (hh28 : h ≤ 28)
    (hw : geom.wotsChains = 128) (hts : geom.targetSum = 192) (hsh : geom.subtreeHeight = h) :
    kpN < 2 ^ h ∧
    verifyWotsLayer geom pub.1 layer tree kpN (stepHmsgOf (stepRegsAt R tD).main)
        ⟨ctr, stepLayerChains R (tD + 5), stepLayerPath R (tD + 455) h⟩ =
      some (stepPermAt R (tD + 455 + 2 * (h - 1) + 1)).b0 ∧
    (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)).curRoot = (stepRegsAt R tD).curRoot ∧
    StepAddrOk (stepRegsAt R (tD + 455 + 2 * (h - 1) + 1)) kpN tree := by
  obtain ⟨hChk, hPack, hSum, _, hCR, hKp, hLo, hHi⟩ := stepDecomp_sem hDec hRem0 hAcc0
  obtain ⟨hm, hhm⟩ : ∃ hm, hm = stepHmsgOf (stepRegsAt R tD).main := ⟨_, rfl⟩
  rw [← hhm] at hChk hPack hSum ⊢
  have hAddr5 : StepAddrOk (stepRegsAt R (tD + 5)) kpN tree :=
    ⟨hKp.trans hAddr.kp, hLo.trans hAddr.lo, hHi.trans hAddr.hi⟩
  have e450 : tD + 5 + 450 = tD + 455 := by omega
  obtain ⟨hd, hSlots, hWork, hCur450R, hAddr450, hCursor⟩ :=
    stepWots_sem hWots hAddr5 hl hk
  rw [e450] at hWork hCur450R hAddr450 hCursor
  have hDigEq : ∀ s a len : Nat, (∀ c < 128, wotsPackSlot c = s ↔ a ≤ c ∧ c < a + len) → s < 5 →
      a + len ≤ 128 → 4 ^ len < goldilocksPrime → wotsPackSlotStart s = a →
      ∀ c, a ≤ c → c < a + len →
        stepChainDigit R (stepChainRow (tD + 5) c) = stepDigit hm c := by
    intro s a len hRange hs haN hLen hStart c hac hcl
    have h1 := hSlots s a len hRange hs haN hLen
    have h2 := hPack s (by omega)
    rw [stepPackFold_slot _ s a len hRange haN hStart] at h2
    rw [h2] at h1
    have hLtD : ∀ x ∈ (List.range' a len).map (fun c => 3 - stepDigit hm c), x < 4 := by
      intro x hx
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
      show 3 - stepDigit hm c' < 4
      omega
    have hLtd : ∀ x ∈ (List.range' a len).map
        (fun c => 3 - stepChainDigit R (stepChainRow (tD + 5) c)), x < 4 := by
      intro x hx
      obtain ⟨c', _, rfl⟩ := List.mem_map.mp hx
      show 3 - stepChainDigit R (stepChainRow (tD + 5) c') < 4
      omega
    have hBound := evalBaseDigits_lt_pow 4 (by decide) _ hLtD
    rw [List.length_map, List.length_range'] at hBound
    rw [Goldilocks.ofNat_val, Nat.mod_eq_of_lt (Nat.lt_trans hBound hLen)] at h1
    have hList := evalBaseDigits_inj 4 (by decide)
      (by rw [List.length_map, List.length_map]) hLtD hLtd h1
    have hc : 3 - stepDigit hm c = 3 - stepChainDigit R (stepChainRow (tD + 5) c) :=
      (List.map_inj_left.mp hList) c (mem_range'_of_bounds len a c hac hcl)
    have hd1 := hd c (by omega)
    have hd2 := stepDigit_le hm c
    omega
  have hDigAll : ∀ c < 128, stepChainDigit R (stepChainRow (tD + 5) c) = stepDigit hm c := by
    intro c hc
    by_cases h0 : c < 26
    · exact hDigEq 0 0 26 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
    by_cases h1 : c < 52
    · exact hDigEq 1 26 26 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
    by_cases h2 : c < 78
    · exact hDigEq 2 52 26 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
    by_cases h3 : c < 103
    · exact hDigEq 3 78 25 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
    · exact hDigEq 4 103 25 (by decide +kernel) (by decide) (by decide) (by decide) rfl c
        (by omega) (by omega)
  have hEnd : stepLayerEndpoints pub R layer tree kpN (tD + 5) =
      recoverAggWotsEndpoints pub.1.pkSeed layer tree kpN 0
        ((List.range' 0 128).map (stepDigit hm)) (stepLayerChains R (tD + 5)) := by
    unfold stepLayerEndpoints stepLayerChains
    rw [List.range_eq_range', recoverAggWotsEndpoints_map]
    apply List.map_congr_left
    intro c hc
    have hb := mem_range'_bounds _ _ _ hc
    unfold stepChainEndpoint
    rw [hDigAll c (by omega)]
  obtain ⟨hKpLt, hWalk, hFr⟩ :=
    stepMerkle_sem (tag := domainMerkleNode)
      (M := fun l => ‹layer * 2 ^ 48 + (l + 1) * 2 ^ 32›) (layerV := layer) (treeV := tree)
      (addr := xmssNodeAddr) (fun l hl' => stepMerkleARow_xmss (hA l hl')) hBin hBnext hLastCur
      hCursor hk hh hh28 (fun l hl' _ L Rr => by
        rw [hAddr450.lo, hAddr450.hi]
        exact stepNodeHashF_xmss _ _ _ _ _ _ _ (by omega) (by omega)
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_trans hk (by decide))))
  refine ⟨hKpLt, ?_, hFr.curRoot.trans (hCur450R.trans hCR),
    ⟨hFr.kp.trans hAddr450.kp, hFr.treeLo.trans hAddr450.lo, hFr.treeHi.trans hAddr450.hi⟩⟩
  have hLen1 : (stepLayerChains R (tD + 5)).length = 128 := by
    unfold stepLayerChains
    rw [List.length_map, List.length_range]
  have hLen2 : (stepLayerPath R (tD + 455) h).length = h := by
    unfold stepLayerPath
    rw [List.length_map, List.length_range]
  unfold verifyWotsLayer
  simp only [hLen1, hLen2, hw, hsh, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    stepDigits_extract geom hm hw hChk, hSum, hts]
  rw [← hEnd, ← hWork]
  exact congrArg some hWalk


theorem stepXmssProgram_chains : ∀ c < 128,
    (buildSignerProgram .xmssPoseidon2).getD (stepChainRow 8 c) .idle =
      .wotsChainStep0 0 c (wotsPackSlot c) := by decide +kernel

theorem stepXmssProgram_merkle : ∀ l < 6,
    (buildSignerProgram .xmssPoseidon2).getD (458 + 2 * l) .idle = .xmssMerkleBlockA 0 l ∧
    (buildSignerProgram .xmssPoseidon2).getD (458 + 2 * l + 1) .idle =
      .xmssMerkleBlockB (l + 1 == 6) (l + 1 == 6) := by decide +kernel

theorem stepXmssR_chain_lane (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (c : Nat) (hc : c < 128) :
    stepAuxLane (stepXmssR pk mu sig) (stepChainRow 8 c) 0 = ls.wotsChains.getD c lane4Zero := by
  have ht : stepChainRow 8 c < 512 := by unfold stepChainRow; omega
  have hop := stepXmssProgram_chains c hc
  have ha : ∀ i < 4, stepAux (stepXmssR pk mu sig) (stepChainRow 8 c) i =
      (ls.wotsChains.getD c lane4Zero).toList.getD i Goldilocks.zero := by
    intro i hi
    rw [stepXmssR_aux pk mu sig _ i ht (by omega) _ hop]
    simp only [stepXmssAux, hlayers, List.getD_cons_zero, hi, ↓reduceIte]
  exact Lane4.ext (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) (ha 3 (by decide))

theorem stepXmssR_path_lane (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (l : Nat) (hl : l < 6) :
    stepAuxLane (stepXmssR pk mu sig) (458 + 2 * l) 2 = ls.merklePath.getD l lane4Zero := by
  have ht : 458 + 2 * l < 512 := by omega
  have hop := (stepXmssProgram_merkle l hl).1
  have ha : ∀ i < 4, stepAux (stepXmssR pk mu sig) (458 + 2 * l) (2 + i) =
      (ls.merklePath.getD l lane4Zero).toList.getD i Goldilocks.zero := by
    intro i hi
    rw [stepXmssR_aux pk mu sig _ (2 + i) ht (by omega) _ hop]
    simp only [stepXmssAux, hlayers, List.getD_cons_zero,
      show ¬2 + i = 0 by omega, show ¬2 + i = 1 by omega,
      show 2 + i < 6 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  exact Lane4.ext (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) (ha 3 (by decide))

theorem stepXmssR_chain_values (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (hlen : ls.wotsChains.length = 128) :
    stepLayerChains (stepXmssR pk mu sig) 8 = ls.wotsChains := by
  apply List.ext_getElem
  · simp only [stepLayerChains, List.length_map, List.length_range, hlen]
  · intro i hi hi'
    have hi128 : i < 128 := by simpa only [stepLayerChains, List.length_map, List.length_range] using hi
    simp only [stepLayerChains, List.getElem_map, List.getElem_range]
    rw [stepXmssR_chain_lane pk mu sig ls hlayers i hi128,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]

theorem stepXmssR_path_values (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (ls : WotsLayerSig) (hlayers : sig.layers = [ls]) (hlen : ls.merklePath.length = 6) :
    stepLayerPath (stepXmssR pk mu sig) 458 6 = ls.merklePath := by
  apply List.ext_getElem
  · simp only [stepLayerPath, List.length_map, List.length_range, hlen]
  · intro i hi hi'
    have hi6 : i < 6 := by simpa only [stepLayerPath, List.length_map, List.length_range] using hi
    simp only [stepLayerPath, List.getElem_map, List.getElem_range]
    rw [stepXmssR_path_lane pk mu sig ls hlayers i hi6,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]


/-- Every constructed Merkle A row already satisfies its guards. -/
theorem stepXmssR_merkleA (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (l : Nat) (hl : l < 6) :
    StepRowSem (pk, mu) (stepXmssR pk mu sig) (.xmssMerkleBlockA 0 l) (458 + 2 * l) :=
  stepXmssR_sem pk mu sig _ _ (by omega) (stepXmssProgram_merkle l hl).1 True.intro

theorem stepXmssR_merkleB (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (l : Nat) (hl : l < 5) :
    StepRowSem (pk, mu) (stepXmssR pk mu sig) (.xmssMerkleBlockB false false) (458 + 2 * l + 1) := by
  have hop := (stepXmssProgram_merkle l (by omega)).2
  rw [show (l + 1 == 6) = false from beq_eq_false_iff_ne.mpr (by omega)] at hop
  exact stepXmssR_sem pk mu sig _ _ (by omega) hop True.intro

theorem stepXmssR_merkleBin (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (l : Nat) (hl : l < 6) :
    (stepXmssR pk mu sig (458 + 2 * l + 1)).stIn =
      stepMerkleBIn (stepRegsAt (stepXmssR pk mu sig) (458 + 2 * l + 1)) := by
  have he := congrArg StepOpRow.stIn (stepXmssR_built pk mu sig (458 + 2 * l + 1) (by omega))
  rw [(stepXmssProgram_merkle l hl).2] at he
  exact he

set_option maxHeartbeats 800000 in
/-- Six constructed halvings end with zero cursor for every native XMSS leaf index. -/
theorem stepXmssR_merkle_cursor (pk : AggValidatorPk) (mu : Digest5) (sig : AggNativeSignature)
    (leaf : Nat) (hleaf : leaf < 64)
    (hc : (stepRegsAt (stepXmssR pk mu sig) 458).cursor = Goldilocks.ofNat leaf) :
    (stepRegsAt (stepXmssR pk mu sig) 469).cursor = Goldilocks.zero := by
  let R := stepXmssR pk mu sig
  have hleafP : leaf < goldilocksPrime := Nat.lt_trans hleaf (by decide)
  have ha : ∀ l < 6, (stepRegsAt R (458 + 2 * l + 1)).cursor =
      Goldilocks.ofNat ((stepRegsAt R (458 + 2 * l)).cursor.val / 2) := by
    intro l hl
    rw [(stepSem_xmssMerkleBlockA (stepXmssR_merkleA pk mu sig l hl)).2.2.2]
    change stepAux R (458 + 2 * l) 1 = _
    rw [stepXmssR_aux pk mu sig _ 1 (by omega) (by decide) _ (stepXmssProgram_merkle l hl).1]
    rfl
  have hbefore : ∀ l, l < 6 → (stepRegsAt R (458 + 2 * l)).cursor = Goldilocks.ofNat (leaf / 2 ^ l) := by
    intro l
    induction l with
    | zero => intro _; simpa only [Nat.pow_zero, Nat.div_one] using hc
    | succ l ih =>
      intro hl
      have hb : stepRegsAt R (458 + 2 * l + 2) = _ :=
        (stepSem_xmssMerkleBlockB_inner (stepXmssR_merkleB pk mu sig l (by omega))).2
      rw [show 458 + 2 * (l + 1) = 458 + 2 * l + 2 by omega, hb]
      change (stepRegsAt R (458 + 2 * l + 1)).cursor = _
      rw [ha l (by omega), ih (by omega), Goldilocks.ofNat_val,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self leaf _) hleafP),
        Nat.div_div_eq_div_mul, Nat.pow_succ]
  have he := ha 5 (by decide)
  rw [hbefore 5 (by decide), Goldilocks.ofNat_val,
    Nat.mod_eq_of_lt (show leaf / 2 ^ 5 < goldilocksPrime by have := Nat.div_le_self leaf (2 ^ 5); omega)] at he
  have hz : leaf / 2 ^ 5 / 2 = 0 := by omega
  rw [hz] at he
  exact he


attribute [local irreducible] stepXmssR

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- Native acceptance establishes the entire non-padding XMSS execution. -/
theorem stepXmssNative_body (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    StepRunAt (pk, computeMessageMu pk msg) (stepXmssR pk (computeMessageMu pk msg) sig)
      (signerProgramBody .xmssPoseidon2) 0 := by
  let mu := computeMessageMu pk msg
  let R := stepXmssR pk mu sig
  obtain ⟨ls, hlayers, hleaf, hV⟩ := stepXmssNative_layer pk msg sig h
  obtain ⟨hchk, hsum, hchains, hpath⟩ := stepXmssNative_digits pk _ ls _ hV
  obtain ⟨hhmsg, hrem0, hacc0, haddr0⟩ := stepXmssR_hmsg pk mu sig ls hlayers hleaf
  rw [← hhmsg] at hchk hsum
  have hdec := stepXmssR_decomp pk mu sig hchk hsum hacc0
  obtain ⟨_, hpack, _, _, hroot8, hkp8, hlo8, hhi8⟩ := stepDecomp_sem hdec hrem0 hacc0
  have hbound := stepForward_pack_bounds _ _ hpack
  have hwots := stepXmssR_wots pk mu sig hbound
  have haddr8 : StepAddrOk (stepRegsAt R 8) sig.statefulLeafIdx 0 :=
    ⟨hkp8.trans haddr0.kp, hlo8.trans haddr0.lo, hhi8.trans haddr0.hi⟩
  have hws := stepWots_sem hwots haddr8 (by decide) (by omega)
  have hcur := stepXmssR_merkle_cursor pk mu sig sig.statefulLeafIdx hleaf hws.2.2.2.2.2
  have hA := stepXmssR_merkleA pk mu sig
  have hBin := stepXmssR_merkleBin pk mu sig
  have hBnext : ∀ l, l + 1 < 6 → stepRegsAt R (458 + 2 * l + 2) =
      { stepRegsAt R (458 + 2 * l + 1) with work := (stepPermAt R (458 + 2 * l + 1)).b0 } := by
    intro l hl
    exact (stepSem_xmssMerkleBlockB_inner (stepXmssR_merkleB pk mu sig l (by omega))).2
  have hLayer := stepLayer_verify_forward (geom := xmssPoseidon2Geom) (ctr := ls.tswCtr)
    (layer := 0) (h := 6) (tD := 3) (kpN := sig.statefulLeafIdx) (tree := 0)
    hdec hwots hrem0 hacc0 haddr0 hA hBin hBnext hcur
    (by decide) (by omega) (by decide) (by decide) rfl rfl rfl
  have hLayerV := hLayer.2.1
  rw [hhmsg, stepXmssR_chain_values pk mu sig ls hlayers hchains,
    stepXmssR_path_values pk mu sig ls hlayers hpath] at hLayerV
  have hV' : verifyWotsLayer xmssPoseidon2Geom pk 0 0 sig.statefulLeafIdx
      (computeHmsgStateful pk sig.rRand mu sig.statefulLeafIdx ls.tswCtr) ls =
        some (stepPermAt R 469).b0 := hLayerV
  have hroot : (stepPermAt R 469).b0 = pk.pkRoot := Option.some.inj (hV'.symm.trans hV)
  have hst : (R 469).stIn = stepXmssInput pk mu (.xmssMerkleBlockB true true)
      (R 469).prevState (stepXmssAux sig (.xmssMerkleBlockB true true) (R 469).prevState) := by
    have he := congrArg StepOpRow.stIn (stepXmssR_built pk mu sig 469 (by decide))
    have hop : (buildSignerProgram .xmssPoseidon2).getD 469 .idle = .xmssMerkleBlockB true true := rfl
    rw [hop] at he
    exact he
  have hroot' : (poseidon2Perm12 (stepXmssInput pk mu (.xmssMerkleBlockB true true)
      (R 469).prevState (stepXmssAux sig (.xmssMerkleBlockB true true) (R 469).prevState))).b0 = pk.pkRoot := by
    rw [← hst]
    exact hroot
  have htop : StepRowSem (pk, mu) R (.xmssMerkleBlockB true true) 469 := by
    apply stepXmssR_sem pk mu sig 469 (.xmssMerkleBlockB true true) (by decide) rfl
    refine ⟨hcur, ?_⟩
    intro i hi
    rcases i with _ | _ | _ | _ | i
    · exact congrArg Lane4.x0 hroot'
    · exact congrArg Lane4.x1 hroot'
    · exact congrArg Lane4.x2 hroot'
    · exact congrArg Lane4.x3 hroot'
    · exact False.elim (by omega)
  have hmerkle : StepRunAt (pk, mu) R (stepMerkleOps 0 6 true) 458 := by
    intro i hi
    change i < 12 at hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    · exact hA 0 (by decide)
    · exact stepXmssR_merkleB pk mu sig 0 (by decide)
    · exact hA 1 (by decide)
    · exact stepXmssR_merkleB pk mu sig 1 (by decide)
    · exact hA 2 (by decide)
    · exact stepXmssR_merkleB pk mu sig 2 (by decide)
    · exact hA 3 (by decide)
    · exact stepXmssR_merkleB pk mu sig 3 (by decide)
    · exact hA 4 (by decide)
    · exact stepXmssR_merkleB pk mu sig 4 (by decide)
    · exact hA 5 (by decide)
    · exact htop
    · exact False.elim (by omega)
  have hpush : StepRunAt (pk, mu) R (pushLayerWotsAndMerkle 0 6 true) 8 := by
    rw [pushLayerWotsAndMerkle_eq]
    apply stepForwardRunAt_append
    · exact hwots
    · rw [stepWotsOps_length]
      exact hmerkle
  unfold signerProgramBody
  apply stepForwardRunAt_append
  · apply stepForwardRunAt_append
    · intro i hi
      change i < 3 at hi
      rcases i with _ | _ | _ | i
      · exact stepXmssR_sem pk mu sig 0 _ (by decide) rfl True.intro
      · exact stepXmssR_sem pk mu sig 1 _ (by decide) rfl True.intro
      · exact stepXmssR_sem pk mu sig 2 _ (by decide) rfl True.intro
      · exact False.elim (by omega)
    · exact hdec
  · exact hpush

theorem stepXmssProgram_idle : ∀ t < 512, 470 ≤ t →
    (buildSignerProgram .xmssPoseidon2).getD t .idle = .idle := by decide +kernel

/-- Native XMSS acceptance constructs an accepted 512-row active signer table. -/
theorem stepXmssRows_of_verify (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    stepOp256TableOk .xmssPoseidon2 [some (pk, computeMessageMu pk msg)]
      (stepXmssRows pk (computeMessageMu pk msg) sig) = true := by
  apply (stepXmssRows_table_iff pk (computeMessageMu pk msg) sig).mpr
  intro i row hr
  have hi : i < 512 := by
    have hh := (List.getElem?_eq_some_iff.mp hr).1
    rwa [stepXmssRows_length] at hh
  have he : row = stepXmssR pk (computeMessageMu pk msg) sig i :=
    Option.some.inj (hr.symm.trans (stepXmssR_at pk _ sig i hi))
  subst row
  by_cases hib : i < 470
  · have hbody := stepXmssNative_body pk msg sig h
    have hiBody : i < (signerProgramBody .xmssPoseidon2).length := by
      rw [buildSignerProgram_length.1]; exact hib
    have hs := hbody i hiBody
    have hop : (buildSignerProgram .xmssPoseidon2).getD i .idle =
        (signerProgramBody .xmssPoseidon2)[i] := by
      unfold buildSignerProgram
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hiBody,
        List.getElem?_eq_getElem hiBody, Option.getD_some]
    rw [hop]
    simpa only [Nat.zero_add] using hs.2.1
  · rw [stepXmssProgram_idle i hi (by omega)]
    rfl


/-- An active committee entry carries its message and signature; `none` is inactive. -/
abbrev StepXmssEntry := Option (AggValidatorPk × List UInt8 × AggNativeSignature)

def stepXmssEntrySlot : StepXmssEntry → StepOpSlot
  | none => none
  | some (pk, msg, _) => some (pk, computeMessageMu pk msg)

def stepXmssEntryRows : StepXmssEntry → List StepOpRow
  | none => stepInactiveRows .xmssPoseidon2
  | some (pk, msg, sig) => stepXmssRows pk (computeMessageMu pk msg) sig

def StepXmssEntryValid : StepXmssEntry → Prop
  | none => True
  | some (pk, msg, sig) => verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true

def stepXmssCommitteeSlots (entries : List StepXmssEntry) : List StepOpSlot :=
  entries.map stepXmssEntrySlot

def stepXmssCommitteeRows (entries : List StepXmssEntry) : List StepOpRow :=
  entries.flatMap stepXmssEntryRows

theorem stepXmssEntry_length (entry : StepXmssEntry) : (stepXmssEntryRows entry).length = 512 := by
  cases entry with
  | none => exact List.length_replicate ..
  | some p => exact stepXmssRows_length ..

theorem stepXmssEntry_table (entry : StepXmssEntry) (h : StepXmssEntryValid entry) :
    stepOp256TableOk .xmssPoseidon2 [stepXmssEntrySlot entry] (stepXmssEntryRows entry) = true := by
  cases entry with
  | none => exact stepInactiveCommittee_table .xmssPoseidon2 1 (by decide)
  | some p => exact stepXmssRows_of_verify p.1 p.2.1 p.2.2 h

theorem stepXmssCommittee_length (entries : List StepXmssEntry) :
    (stepXmssCommitteeRows entries).length = entries.length * 512 := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    change (stepXmssEntryRows e ++ stepXmssCommitteeRows es).length = (es.length + 1) * 512
    rw [List.length_append, stepXmssEntry_length, ih, Nat.add_mul]
    omega

/-- Indexing a concatenation of fixed-width signer blocks. -/
theorem stepXmssCommittee_get (entries : List StepXmssEntry) (i : Nat)
    (hi : i / 512 < entries.length) :
    (stepXmssCommitteeRows entries)[i]? =
      (stepXmssEntryRows (entries.getD (i / 512) none))[i % 512]? := by
  induction entries generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    change (stepXmssEntryRows e ++ stepXmssCommitteeRows es)[i]? = _
    by_cases hlt : i < 512
    · rw [List.getElem?_append_left (by rw [stepXmssEntry_length]; exact hlt),
        Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, List.getD_cons_zero]
    · rw [List.getElem?_append_right (by rw [stepXmssEntry_length]; omega), stepXmssEntry_length]
      have hk : (i - 512) / 512 < es.length := by simp only [List.length_cons] at hi; omega
      rw [ih (i - 512) hk]
      have hd : i / 512 = (i - 512) / 512 + 1 := by omega
      have hm : i % 512 = (i - 512) % 512 := by omega
      rw [hd, hm, List.getD_cons_succ]

theorem stepXmssEntry_boundary (entry : StepXmssEntry) (hv : StepXmssEntryValid entry)
    (j : Nat) (row : StepOpRow) (hr : (stepXmssEntryRows entry)[j]? = some row) :
    (∀ s < 44, j % 512 = 0 → row.prevState.getD s Goldilocks.zero = Goldilocks.zero) ∧
    (∀ s < 44, j % 512 + 1 = 512 → row.nextState.getD s Goldilocks.zero = Goldilocks.zero) := by
  have hz := stepOp256TableOk_row_at .xmssPoseidon2 [stepXmssEntrySlot entry] _ j row
    (stepXmssEntry_table entry hv) hr
  simp only [stepOp256RowResiduals, allZeroGoldilocks_append, Bool.and_eq_true] at hz
  exact (stepOpBoundaryResiduals_iff 512 (j % 512) row).mp hz.1.2

/-- Native acceptance of each active entry constructs a table with arbitrary inactive slots. -/
theorem stepXmssCommittee_of_verify (entries : List StepXmssEntry)
    (hne : 0 < entries.length) (hv : ∀ entry ∈ entries, StepXmssEntryValid entry) :
    stepOp256TableOk .xmssPoseidon2 (stepXmssCommitteeSlots entries)
      (stepXmssCommitteeRows entries) = true := by
  have hlen := stepXmssCommittee_length entries
  have hm : ∀ k, k < entries.length → entries.getD k none ∈ entries := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact List.getElem_mem hk
  have hloc : ∀ k, k < entries.length →
      stepOp256TableOk .xmssPoseidon2 [stepXmssEntrySlot (entries.getD k none)]
        (stepXmssEntryRows (entries.getD k none)) = true :=
    fun k hk => stepXmssEntry_table _ (hv _ (hm k hk))
  have hidx : ∀ i row, (stepXmssCommitteeRows entries)[i]? = some row → i / 512 < entries.length := by
    intro i row hr
    have hi := (List.getElem?_eq_some_iff.mp hr).1
    rw [hlen] at hi
    omega
  apply (stepOp256TableOk_iff_rows _ _ _).mpr
  refine ⟨by simpa only [stepXmssCommitteeSlots, List.length_map] using hne,
    by simpa only [stepXmssCommitteeSlots, List.length_map, stepOpRowsPerSigner] using hlen, ?_, ?_, ?_⟩
  · intro row hr
    obtain ⟨entry, he, hr⟩ := List.mem_flatMap.mp hr
    exact ((stepOp256TableOk_iff_rows _ _ _).mp (stepXmssEntry_table entry (hv entry he))).2.2.1 row hr
  · intro i row hr
    have hk := hidx i row hr
    have hrow := hr
    rw [stepXmssCommittee_get entries i hk] at hrow
    have hz := stepOp256TableOk_row_at .xmssPoseidon2 _ _ (i % 512) row (hloc (i / 512) hk) hrow
    have hj : i % 512 < 512 := Nat.mod_lt _ (by decide)
    simp only [stepOpRowsPerSigner, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, List.getD_cons_zero] at hz
    have hs : (stepXmssCommitteeSlots entries).getD (i / 512) none =
        stepXmssEntrySlot (entries.getD (i / 512) none) := by
      simp only [stepXmssCommitteeSlots, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
    change allZeroGoldilocks (stepOp256RowResiduals .xmssPoseidon2
      ((stepXmssCommitteeSlots entries).getD (i / 512) none) (i % 512) row) = true
    rw [hs]
    exact hz
  · intro i r r' hr hr' s hs
    have hk := hidx i r hr
    have hk' := hidx (i + 1) r' hr'
    rw [stepXmssCommittee_get entries i hk] at hr
    rw [stepXmssCommittee_get entries (i + 1) hk'] at hr'
    by_cases hlast : i % 512 = 511
    · have hz := stepXmssEntry_boundary _ (hv _ (hm (i / 512) hk)) (i % 512) r hr
      have hz' := stepXmssEntry_boundary _ (hv _ (hm ((i + 1) / 512) hk')) ((i + 1) % 512) r' hr'
      rw [hz.2 s hs (by omega), hz'.1 s hs (by omega)]
    · have hd : (i + 1) / 512 = i / 512 := by omega
      have hj : (i + 1) % 512 = i % 512 + 1 := by omega
      rw [hd, hj] at hr'
      exact ((stepOp256TableOk_iff_rows _ _ _).mp (hloc (i / 512) hk)).2.2.2.2
        (i % 512) r r' hr hr' s hs


/-- Associate signatures and messages with the public slot indices. -/
def stepXmssSlotEntries (slots : List StepOpSlot) (msg : Nat → List UInt8)
    (sig : Nat → AggNativeSignature) : List StepXmssEntry :=
  (List.range slots.length).map fun i =>
    (slots.getD i none).map fun pub => (pub.1, msg i, sig i)

def stepXmssSlotsRows (slots : List StepOpSlot) (msg : Nat → List UInt8)
    (sig : Nat → AggNativeSignature) : List StepOpRow :=
  stepXmssCommitteeRows (stepXmssSlotEntries slots msg sig)

/-- Direct public-slot interface, permitting active and inactive slots in any order. -/
theorem stepXmssSlotsRows_of_verify (slots : List StepOpSlot) (msg : Nat → List UInt8)
    (sig : Nat → AggNativeSignature) (hne : 0 < slots.length)
    (h : ∀ i pub, slots[i]? = some (some pub) →
      pub.2 = computeMessageMu pub.1 (msg i) ∧
      verifyAggNativeSig xmssPoseidon2Geom pub.1 (msg i) (sig i) = true) :
    stepOp256TableOk .xmssPoseidon2 slots (stepXmssSlotsRows slots msg sig) = true := by
  have hs : stepXmssCommitteeSlots (stepXmssSlotEntries slots msg sig) = slots := by
    apply List.ext_getElem
    · simp only [stepXmssCommitteeSlots, stepXmssSlotEntries, List.length_map, List.length_range]
    · intro i hi hi'
      simp only [stepXmssCommitteeSlots, stepXmssSlotEntries, List.getElem_map, List.getElem_range]
      have hd : slots.getD i none = slots[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      rw [hd]
      cases he : slots[i] with
      | none => rfl
      | some pub =>
        have hh := h i pub (by rw [List.getElem?_eq_getElem hi', he])
        change some (pub.1, computeMessageMu pub.1 (msg i)) = some pub
        rw [← hh.1]
  have hv : ∀ entry ∈ stepXmssSlotEntries slots msg sig, StepXmssEntryValid entry := by
    intro entry he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    have hi' : i < slots.length := List.mem_range.mp hi
    have hd : slots.getD i none = slots[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    rw [hd]
    cases he : slots[i] with
    | none => exact True.intro
    | some pub => exact (h i pub (by rw [List.getElem?_eq_getElem hi', he])).2
  have ht := stepXmssCommittee_of_verify (stepXmssSlotEntries slots msg sig)
    (by simpa only [stepXmssSlotEntries, List.length_map, List.length_range] using hne) hv
  rw [hs] at ht
  exact ht

theorem stepXmssNative_profile (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) : pk.profile = .xmssPoseidon2 := by
  unfold verifyAggNativeSig at h
  split at h
  · contradiction
  · rename_i hc
    have hf := Bool.eq_false_iff.mpr hc
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hf
    exact hf.1.1.2

/-- An accepted signature survives the complete native-to-table-to-native round trip. -/
theorem stepXmssRows_roundTrip (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    verifyAggNativeSig xmssPoseidon2Geom pk msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2 (stepXmssRows pk (computeMessageMu pk msg) sig) 0)) = true :=
  stepOp256TableOk_xmss_extract _ _ 0 (pk, computeMessageMu pk msg) msg
    (stepXmssRows_of_verify pk msg sig h) rfl (stepXmssNative_profile pk msg sig h) rfl

set_option maxRecDepth 4096 in
/-- The remaining execution checks are consequences of the original guard equations. -/
theorem stepXmss_checks_of_seed_guards (pk : AggValidatorPk) (mu : Digest5)
    (sig : AggNativeSignature) (op : StepOp) (prev : List Goldilocks)
    (hg : allZeroGoldilocks (stepOpGuardResiduals (stepOpKindAndC0 op).1
      (Goldilocks.ofNat (stepOpKindAndC0 op).2)
      (stepOpRowInputs (pk, mu) (stepXmssSeedRow pk mu sig op prev))) = true) :
    StepXmssChecks pk mu sig op prev := by
  cases op <;> try exact True.intro
  case hmsgDecompLimb l =>
    simp only [stepOpKindAndC0, stepOpGuardResiduals, allZeroGoldilocks_append,
      Bool.and_eq_true] at hg
    refine ⟨(stepLimb63Decomp_allZero_iff _ _).mp hg.1 |>.1, ?_⟩
    intro hl
    have hh := hg.2
    simp only [hl, ↓reduceIte, allZeroGoldilocks, List.all_cons, List.all_nil,
      Bool.and_true, beq_iff_eq, g_sub_eq_zero_iff] at hh
    simpa only [hl] using hh
  case wotsTellPairAbsorb pair =>
    intro hp
    simp only [stepOpKindAndC0, stepOpGuardResiduals, hp, beq_self_eq_true,
      ↓reduceIte, allZeroGoldilocks_append, Bool.and_eq_true] at hg
    exact (allZero_map_iff _ _).mp hg.1
  case xmssMerkleBlockB a b =>
    cases a <;> cases b <;> try exact True.intro
    simp only [stepOpKindAndC0, stepOpGuardResiduals, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, allZeroGoldilocks_append, Bool.and_eq_true] at hg
    constructor
    · have hh := hg.2.1
      simp only [allZeroGoldilocks, List.all_cons, List.all_nil, Bool.and_true,
        beq_iff_eq] at hh
      exact hh
    · intro i hi
      have hh := g_sub_eq_zero_iff.mp ((allZero_map_iff _ _).mp hg.2.2 i hi)
      have hp := stepOp256_groupA_exact
        (stepXmssSeedRow pk mu sig (.xmssMerkleBlockB true true) prev)
        (stepOpHonestPermutationRow_groupA ..)
      change (stepOpPermTrace _).1.toList.getD i Goldilocks.zero = _ at hh
      rw [hp] at hh
      exact hh

/-- Native acceptance discharges every arithmetic and terminal execution check. -/
theorem stepXmssChecks_of_verify (pk : AggValidatorPk) (msg : List UInt8)
    (sig : AggNativeSignature) (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true)
    (i : Nat) (row : StepOpRow)
    (hr : (stepXmssRows pk (computeMessageMu pk msg) sig)[i]? = some row) :
    StepXmssChecks pk (computeMessageMu pk msg) sig
      ((buildSignerProgram .xmssPoseidon2).getD i .idle) row.prevState := by
  let mu := computeMessageMu pk msg
  have hg := (stepXmssRows_table_iff pk mu sig).mp (stepXmssRows_of_verify pk msg sig h) i row hr
  obtain ⟨op, state, hop, he⟩ := stepForwardRun_at (pk, mu) (stepXmssCells pk mu sig)
    (buildSignerProgram .xmssPoseidon2) stepForwardZero i row hr
  have hopD : (buildSignerProgram .xmssPoseidon2).getD i .idle = op := by
    rw [List.getD_eq_getElem?_getD, hop]; rfl
  rw [hopD, he] at hg ⊢
  change allZeroGoldilocks (stepOpGuardResiduals _ _
    (stepOpRowInputs (pk, mu) (populateStepOpNext _ _ _ (stepXmssSeedRow pk mu sig op state)))) = true at hg
  rw [populateStepOpNext_inputs, stepOpGuardResiduals_congr_next] at hg
  exact stepXmss_checks_of_seed_guards pk mu sig op state hg

end StepOpForward

end Qsag
