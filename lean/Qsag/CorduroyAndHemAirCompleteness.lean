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
