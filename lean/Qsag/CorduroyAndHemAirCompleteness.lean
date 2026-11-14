module
/-
# Qsag.CorduroyAndHemAirCompleteness — Algebraic `Corduroy` Hypertree & `Hem` Opcode Semantics

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

Active-slot population, the full machine-to-`verifyAggNativeSig` simulation, and the bridge to
serialized signer-witness rows remain open. The custody geometry above is distinct from the
aggregation geometry (16 layers, 32 FORS trees of height 8); the two must not be identified.
-/

public import Qsag.Constructive
public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.Poseidon2
import all Qsag.Poseidon2
public import Qsag.HashSigs
import all Qsag.HashSigs
public import Qsag.ThresholdMpc
import all Qsag.ThresholdMpc
public import Qsag.Aggregation
import all Qsag.Aggregation
public import Qsag.SuccinctAggregationIop
import all Qsag.SuccinctAggregationIop
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
