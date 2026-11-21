module
/-
# Qsag.Protocol.Signing.AdrsSeparationGuardTeeth — Probability-`1` `HashAdrs` Separation Refutation

Pairs `FullAdaptiveEufCma` against a probability-`1` (`∀ ω, win ω = true`) adaptive forgery
refutation when `HashAdrs` leaf/layer tweak separation is zeroed out (`Guard (c)` —
`zeroKpLayerOfSuite`), while keeping both `BeltLatch` ON and `checkTargetSum` ON.
-/

public import Qsag.Protocol.Signing.ClosedGameGuardTeeth
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

def zeroKpLayerOfSuite (suite : TweakableHashSuite) : TweakableHashSuite where
  suiteId := suite.suiteId ++ [0x00]
  rawHash raw :=
    match parseThPreimage raw with
    | some (role, pkSeed, adrs, args) =>
      suite.rawHash (thPreimage role pkSeed { adrs with layer := 0, keyPair := 0 } args)
    | none => suite.rawHash raw
  rawHash_len raw := by
    split
    · exact suite.rawHash_len _
    · exact suite.rawHash_len _

theorem zeroKpLayerOfSuite_thCall (suite : TweakableHashSuite)
    (role pkSeed : List UInt8) (adrs : HashAdrs) (args : List (List UInt8)) :
    thCall (zeroKpLayerOfSuite suite) role pkSeed adrs args =
      thCall suite role pkSeed { adrs with layer := 0, keyPair := 0 } args := by
  rw [thCall_eq, thCall_eq]
  unfold zeroKpLayerOfSuite
  dsimp only
  rw [parseThPreimage_thPreimage]
  dsimp only

def symMerkleSuite : TweakableHashSuite where
  suiteId := "QSAG.PQ.SUITE.SYM.MERKLE/v1".toByteArray.toList
  rawHash raw :=
    match parseThPreimage raw with
    | some (role, _, adrs, args) =>
      if role = tagThH then
        match args with
        | [left, right] =>
          if adrs.layer = 0 ∧ adrs.tree = 0 ∧ adrs.kind = .tree then
            if adrs.chainIdx.toNat = 1 ∧ adrs.hashStep.toNat < 2 then
              if left.headD 0 = 0xC0 ∧ left.drop 8 = List.replicate 24 0x00 ∧ left.length = 32 ∧
                  right.headD 0 = 0xC0 ∧ right.drop 8 = List.replicate 24 0x00 ∧
                  right.length = 32 then
                [0xD1, UInt8.ofNat adrs.hashStep.toNat] ++
                  (left.drop 2).take 6 ++ (right.drop 2).take 6 ++ List.replicate 18 0x00
              else 0xFF :: List.replicate 31 0x00
            else if adrs.chainIdx.toNat = 2 ∧ adrs.hashStep.toNat = 0 then
              if left.take 2 = [0xD1, 0] ∧ left.drop 14 = List.replicate 18 0x00 ∧
                  left.length = 32 ∧ right.take 2 = [0xD1, 1] ∧
                  right.drop 14 = List.replicate 18 0x00 ∧ right.length = 32 then
                [0xD2, 0] ++ (left.drop 2).take 12 ++ (right.drop 2).take 12 ++
                  List.replicate 6 0x00
              else 0xFF :: List.replicate 31 0x00
            else 0xFF :: List.replicate 31 0x00
          else 0xFF :: List.replicate 31 0x00
        | _ => 0xFF :: List.replicate 31 0x00
      else poly257MultiLeafSuite.rawHash raw
    | none => poly257MultiLeafSuite.rawHash raw
  rawHash_len raw := by
    split
    · split
      · match _ : _ with
        | [left, right] =>
          split
          · split
            · split
              · rename_i hc
                have hL : ((left.drop 2).take 6).length = 6 := by
                  rw [List.length_take, List.length_drop, hc.2.2.1]; decide
                have hR : ((right.drop 2).take 6).length = 6 := by
                  rw [List.length_take, List.length_drop, hc.2.2.2.2.2]; decide
                simp [hL, hR]
              · rfl
            · split
              · split
                · rename_i hc
                  have hL : ((left.drop 2).take 12).length = 12 := by
                    rw [List.length_take, List.length_drop, hc.2.2.1]; decide
                  have hR : ((right.drop 2).take 12).length = 12 := by
                    rw [List.length_take, List.length_drop, hc.2.2.2.2.2]; decide
                  simp [hL, hR]
                · rfl
              · rfl
          · rfl
        | [] | [_] | _ :: _ :: _ :: _ => rfl
      · exact poly257MultiLeafSuite.rawHash_len raw
    · exact poly257MultiLeafSuite.rawHash_len raw

private theorem symMerkleSuite_nonThH_eq (role pkSeed : List UInt8) (adrs : HashAdrs)
    (args : List (List UInt8)) (hNe : role ≠ tagThH) :
    thCall symMerkleSuite role pkSeed adrs args =
      thCall poly257MultiLeafSuite role pkSeed adrs args := by
  rw [thCall_eq, thCall_eq]; unfold symMerkleSuite; dsimp only
  rw [parseThPreimage_thPreimage]; dsimp only; rw [ite_eq_right hNe]

private theorem symMerkleSuite_role_ne :
    tagPrf ≠ tagThH ∧ tagPrfMsg ≠ tagThH ∧ tagHPre ≠ tagThH ∧
    tagHMsg ≠ tagThH ∧ tagThF ≠ tagThH ∧ tagThTl ≠ tagThH := by
  simp only [tagPrf.public_eqs, tagPrfMsg.public_eqs, tagHPre.public_eqs, tagHMsg.public_eqs,
    tagThF.public_eqs, tagThTl.public_eqs, tagThH.public_eqs]; decide +kernel

private theorem symMerkleSuite_computeWotsPk_eq (sk : PqSecretKey) (l : UInt32) (t : UInt64)
    (kp : Nat) :
    computeWotsPk symMerkleSuite multiLeaf4JortsParams sk l t kp =
      computeWotsPk poly257MultiLeafSuite multiLeaf4JortsParams sk l t kp := by
  rw [computeWotsPk_eq, computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq,
    symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.2.2]
  congr 1; apply List.map_congr_left; intro r _
  have hSec : wotsSecretBase symMerkleSuite sk l t kp r =
      wotsSecretBase poly257MultiLeafSuite sk l t kp r := by
    rw [wotsSecretBase_eq, wotsSecretBase_eq, thSecretPrf_eq, thSecretPrf_eq]
    exact symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.1
  have hSteps : ∀ (k st : Nat) (x : List UInt8),
      wotsChainSteps symMerkleSuite sk.pkSeed l t kp r st k x =
        wotsChainSteps poly257MultiLeafSuite sk.pkSeed l t kp r st k x := by
    intro k; induction k with
    | zero => intro st x; rw [wotsChainSteps_zero, wotsChainSteps_zero]
    | succ k' ih =>
      intro st x; rw [wotsChainSteps_succ, wotsChainSteps_succ]; dsimp only
      rw [thChainF_eq, thChainF_eq, symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.2.1]
      exact ih (st + 1) _
  rw [hSec, hSteps]

private theorem symMerkleSuite_thNodeH_h1 (pkSeed : List UInt8) (kp : UInt32) (idx : Nat)
    (left right : List UInt8) (hIdx : idx < 2)
    (hL : left.headD 0 = 0xC0 ∧ left.drop 8 = List.replicate 24 0x00 ∧ left.length = 32)
    (hR : right.headD 0 = 0xC0 ∧ right.drop 8 = List.replicate 24 0x00 ∧ right.length = 32) :
    thNodeH symMerkleSuite pkSeed ⟨0, 0, .tree, kp, 1, UInt32.ofNat idx⟩ left right =
      [0xD1, UInt8.ofNat idx] ++
        (left.drop 2).take 6 ++ (right.drop 2).take 6 ++ List.replicate 18 0x00 := by
  rw [thNodeH_eq, thCall_eq]; unfold symMerkleSuite; dsimp only
  rw [parseThPreimage_thPreimage]; dsimp only; rw [ite_eq_left rfl]
  have hIdx32 : (UInt32.ofNat idx).toNat = idx := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hc1 : (1 : UInt32).toNat = 1 := rfl
  simp only [hc1, hIdx32, hIdx, and_self, ↓reduceIte]
  exact ite_eq_left ⟨hL.1, hL.2.1, hL.2.2, hR.1, hR.2.1, hR.2.2⟩

private theorem symMerkleSuite_thNodeH_h2 (pkSeed : List UInt8) (kp : UInt32)
    (left right : List UInt8)
    (hL : left.take 2 = [0xD1, 0] ∧ left.drop 14 = List.replicate 18 0x00 ∧ left.length = 32)
    (hR : right.take 2 = [0xD1, 1] ∧ right.drop 14 = List.replicate 18 0x00 ∧ right.length = 32) :
    thNodeH symMerkleSuite pkSeed ⟨0, 0, .tree, kp, 2, 0⟩ left right =
      [0xD2, 0] ++ (left.drop 2).take 12 ++ (right.drop 2).take 12 ++ List.replicate 6 0x00 := by
  rw [thNodeH_eq, thCall_eq]; unfold symMerkleSuite; dsimp only
  rw [parseThPreimage_thPreimage]; dsimp only; rw [ite_eq_left rfl]
  have hc2 : (2 : UInt32).toNat = 2 := rfl
  have hs0 : (0 : UInt32).toNat = 0 := rfl
  simp only [hc2, hs0, (by decide : ¬ (2 = 1 ∧ 0 < 2)), and_self, ↓reduceIte]
  exact ite_eq_left ⟨hL.1, hL.2.1, hL.2.2, hR.1, hR.2.1, hR.2.2⟩

private theorem leafFromTbl_shape (tbl : Nat → Nat → UInt8 × UInt8) (kp : Nat) :
    (leafFromTbl tbl kp).headD 0 = 0xC0 ∧
    (leafFromTbl tbl kp).drop 8 = List.replicate 24 0x00 ∧
    (leafFromTbl tbl kp).length = 32 ∧
    ((leafFromTbl tbl kp).drop 2).take 6 = packLeaf3 [tbl kp 0, tbl kp 1, tbl kp 2] := by
  rw [leafFromTbl.public_eqs, packLeaf3.public_eqs]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem node1FromTbl_shape (tbl : Nat → Nat → UInt8 × UInt8) (idx : Nat) :
    (node1FromTbl tbl idx).take 2 = [0xD1, UInt8.ofNat idx] ∧
    (node1FromTbl tbl idx).drop 14 = List.replicate 18 0x00 ∧
    (node1FromTbl tbl idx).length = 32 ∧
    ((node1FromTbl tbl idx).drop 2).take 12 =
      packLeaf3 [tbl (2 * idx) 0, tbl (2 * idx) 1, tbl (2 * idx) 2] ++
      packLeaf3 [tbl (2 * idx + 1) 0, tbl (2 * idx + 1) 1, tbl (2 * idx + 1) 2] := by
  rw [node1FromTbl.public_eqs, packLeaf3.public_eqs, packLeaf3.public_eqs]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem symMerkleSuite_subtreeRoot (sk : PqSecretKey) :
    computeXmssSubtreeRoot symMerkleSuite multiLeaf4JortsParams sk 0 0 =
      rootFromTbl (honestSlotHiLo sk) := by
  rw [computeXmssSubtreeRoot_eq]
  have hSubH : multiLeaf4JortsParams.subtreeHeight = 2 := rfl
  have hc1 : UInt32.ofNat (0 + 1) = 1 := rfl
  have hc2 : UInt32.ofNat (1 + 1) = 2 := rfl
  have hu0 : UInt32.ofNat 0 = 0 := rfl
  rw [hSubH, computeMerkleNode_succ, computeMerkleNode_succ, computeMerkleNode_succ,
    computeMerkleNode_zero, computeMerkleNode_zero, computeMerkleNode_zero, computeMerkleNode_zero]
  dsimp only
  rw [hc1, hc2, hu0,
    symMerkleSuite_computeWotsPk_eq, poly257MultiLeaf_computeWotsPk_eq sk (by decide : 0 < 4),
    symMerkleSuite_computeWotsPk_eq, poly257MultiLeaf_computeWotsPk_eq sk (by decide : 1 < 4),
    symMerkleSuite_computeWotsPk_eq, poly257MultiLeaf_computeWotsPk_eq sk (by decide : 2 < 4),
    symMerkleSuite_computeWotsPk_eq, poly257MultiLeaf_computeWotsPk_eq sk (by decide : 3 < 4)]
  have hL0 := leafFromTbl_shape (honestSlotHiLo sk) 0
  have hL1 := leafFromTbl_shape (honestSlotHiLo sk) 1
  have hL2 := leafFromTbl_shape (honestSlotHiLo sk) 2
  have hL3 := leafFromTbl_shape (honestSlotHiLo sk) 3
  have hN0Eq : thNodeH symMerkleSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat 0⟩
      (leafFromTbl (honestSlotHiLo sk) 0) (leafFromTbl (honestSlotHiLo sk) 1) =
      node1FromTbl (honestSlotHiLo sk) 0 := by
    rw [symMerkleSuite_thNodeH_h1 sk.pkSeed 0 0 _ _ (by decide)
      ⟨hL0.1, hL0.2.1, hL0.2.2.1⟩ ⟨hL1.1, hL1.2.1, hL1.2.2.1⟩,
      hL0.2.2.2, hL1.2.2.2, node1FromTbl.public_eqs]; rfl
  have hN1Eq : thNodeH symMerkleSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat 1⟩
      (leafFromTbl (honestSlotHiLo sk) 2) (leafFromTbl (honestSlotHiLo sk) 3) =
      node1FromTbl (honestSlotHiLo sk) 1 := by
    rw [symMerkleSuite_thNodeH_h1 sk.pkSeed 0 1 _ _ (by decide)
      ⟨hL2.1, hL2.2.1, hL2.2.2.1⟩ ⟨hL3.1, hL3.2.1, hL3.2.2.1⟩,
      hL2.2.2.2, hL3.2.2.2, node1FromTbl.public_eqs]; rfl
  rw [show (0 : UInt32) = UInt32.ofNat 0 from rfl] at *
  rw [hN0Eq, hN1Eq]
  have hM0 := node1FromTbl_shape (honestSlotHiLo sk) 0
  have hM1 := node1FromTbl_shape (honestSlotHiLo sk) 1
  rw [symMerkleSuite_thNodeH_h2 sk.pkSeed (UInt32.ofNat 0) _ _
    ⟨hM0.1, hM0.2.1, hM0.2.2.1⟩ ⟨hM1.1, hM1.2.1, hM1.2.2.1⟩,
    hM0.2.2.2, hM1.2.2.2, rootFromTbl.public_eqs]
  simp [List.append_assoc]

private theorem symMerkleSuite_derivePublicKey (sk : PqSecretKey) :
    derivePublicKey symMerkleSuite multiLeaf4JortsParams sk =
      derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk := by
  rw [derivePublicKey_poly257MultiLeaf, pkFromTbl.public_eqs]
  unfold derivePublicKey
  have hTop : UInt32.ofNat (multiLeaf4JortsParams.numLayers - 1) = 0 := rfl
  rw [hTop, symMerkleSuite_subtreeRoot]

private theorem symMerkleSuite_authPath_eq (sk : PqSecretKey) {kp : Nat} (hkp : kp < 4) :
    buildMerkleAuthPathKp symMerkleSuite sk.pkSeed 0 0 .tree 0
      (computeWotsPk symMerkleSuite multiLeaf4JortsParams sk 0 0) 2 0 0 kp =
      authPathFromTbl (honestSlotHiLo sk) kp := by
  have hCases : kp = 0 ∨ kp = 1 ∨ kp = 2 ∨ kp = 3 := by omega
  have hc1 : UInt32.ofNat (0 + 1) = 1 := rfl
  have hL0 := leafFromTbl_shape (honestSlotHiLo sk) 0
  have hL1 := leafFromTbl_shape (honestSlotHiLo sk) 1
  have hL2 := leafFromTbl_shape (honestSlotHiLo sk) 2
  have hL3 := leafFromTbl_shape (honestSlotHiLo sk) 3
  have hN0Eq : thNodeH symMerkleSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat 0⟩
      (leafFromTbl (honestSlotHiLo sk) 0) (leafFromTbl (honestSlotHiLo sk) 1) =
      node1FromTbl (honestSlotHiLo sk) 0 := by
    rw [symMerkleSuite_thNodeH_h1 sk.pkSeed 0 0 _ _ (by decide)
      ⟨hL0.1, hL0.2.1, hL0.2.2.1⟩ ⟨hL1.1, hL1.2.1, hL1.2.2.1⟩,
      hL0.2.2.2, hL1.2.2.2, node1FromTbl.public_eqs]; rfl
  have hN1Eq : thNodeH symMerkleSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat 1⟩
      (leafFromTbl (honestSlotHiLo sk) 2) (leafFromTbl (honestSlotHiLo sk) 3) =
      node1FromTbl (honestSlotHiLo sk) 1 := by
    rw [symMerkleSuite_thNodeH_h1 sk.pkSeed 0 1 _ _ (by decide)
      ⟨hL2.1, hL2.2.1, hL2.2.2.1⟩ ⟨hL3.1, hL3.2.1, hL3.2.2.1⟩,
      hL2.2.2.2, hL3.2.2.2, node1FromTbl.public_eqs]; rfl
  rcases hCases with rfl | rfl | rfl | rfl <;>
    (rw [buildMerkleAuthPathKp.public_eq_2]; dsimp only;
     simp only [(by decide : 0 < 2 ^ 1), (by decide : 1 < 2 ^ 1),
       (by decide : ¬ (2 < 2 ^ 1)), (by decide : ¬ (3 < 2 ^ 1)), ↓reduceIte];
     rw [buildMerkleAuthPathKp.public_eq_2]; dsimp only;
     simp only [(by decide : 0 < 2 ^ 0), (by decide : ¬ (1 < 2 ^ 0)),
       (by decide : 2 - 2 < 2 ^ 0), (by decide : ¬ (3 - 2 < 2 ^ 0)), ↓reduceIte];
     rw [buildMerkleAuthPathKp.public_eq_1, computeMerkleNodeKp_succ, computeMerkleNodeKp_zero,
       computeMerkleNodeKp_zero, computeMerkleNodeKp_zero, hc1];
     dsimp only;
     rw [symMerkleSuite_computeWotsPk_eq, symMerkleSuite_computeWotsPk_eq,
       symMerkleSuite_computeWotsPk_eq];
     try rw [poly257MultiLeaf_computeWotsPk_eq sk (by decide : 0 < 4)];
     try rw [poly257MultiLeaf_computeWotsPk_eq sk (by decide : 1 < 4)];
     try rw [poly257MultiLeaf_computeWotsPk_eq sk (by decide : 2 < 4)];
     try rw [poly257MultiLeaf_computeWotsPk_eq sk (by decide : 3 < 4)];
     first | (rw [hN1Eq, authPathFromTbl.public_eqs]; rfl)
           | (rw [hN0Eq, authPathFromTbl.public_eqs]; rfl))

private theorem symMerkleSuite_prodSignQuery_eq (sk : PqSecretKey) (q : ProdSigningQuery) :
    prodSignQuery symMerkleSuite multiLeaf4JortsParams sk q =
      prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams sk q := by
  rw [prodSignQuery_eq, prodSignQuery_eq]
  simp only [multiLeaf4JortsParams.public_eqs, ↓reduceIte]
  rw [evalProductionStatefulSign_eq, evalProductionStatefulSign_eq, symMerkleSuite_derivePublicKey]
  if hEpGe : 4 ≤ q.epoch then
    have hOut : (!true || !decide (q.epoch < 2 ^ 2)) = true := by
      have hN : ¬ (q.epoch < 2 ^ 2) := by omega
      simp [PqHashParams.productionWellFormed.public_eqs,
        PqHashParams.productionLeafIdxInRange.public_eqs, hN]
    simp only [multiLeaf4JortsParams.public_eqs,
      PqHashParams.productionWellFormed.public_eqs,
      PqHashParams.productionLeafIdxInRange.public_eqs]
    rw [ite_eq_left hOut, ite_eq_left hOut]
  else
    have hEpLt : q.epoch < 4 := by omega
    have hNotOut : ¬ ((!true || !decide (q.epoch < 2 ^ 2)) = true) := by simp [hEpLt]
    simp only [multiLeaf4JortsParams.public_eqs,
      PqHashParams.productionWellFormed.public_eqs,
      PqHashParams.productionLeafIdxInRange.public_eqs]
    rw [ite_eq_right hNotOut, ite_eq_right hNotOut]
    dsimp only
    rw [symMerkleSuite_derivePublicKey]
    have hPre : ∀ msg, thPreHash symMerkleSuite sk.pkSeed
        (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot msg =
        thPreHash poly257MultiLeafSuite sk.pkSeed
          (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot msg := by
      intro msg; rw [thPreHash_eq, thPreHash_eq]
      exact symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.1
    have hPrf : ∀ mu, thPrfMsg symMerkleSuite sk.skPrf q.randomness mu =
        thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness mu := by
      intro mu; rw [thPrfMsg_eq, thPrfMsg_eq]
      exact symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.1
    rw [hPre, hPrf, signProductionHypertreeCore_def, signProductionHypertreeCore_def]
    let pk := derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk
    let mu := thPreHash poly257MultiLeafSuite pk.pkSeed pk.pkRoot q.message
    let rRand := thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness mu
    change (match (if multiLeaf4JortsParams.statefulJorts then some ([], mu) else _) with
        | none => none | some _ => _) =
      (match (if multiLeaf4JortsParams.statefulJorts then some ([], mu) else _) with
        | none => none | some _ => _)
    have hStTrue : multiLeaf4JortsParams.statefulJorts = true := rfl
    have hNumL : multiLeaf4JortsParams.numLayers = 1 := rfl
    rw [hStTrue]
    dsimp only [↓reduceIte]
    rw [hNumL]
    have hLayersEq :
        signProductionHypertreeLayers symMerkleSuite multiLeaf4JortsParams sk pk.pkRoot rRand
          q.grindLimit 0 q.epoch mu 1 =
        signProductionHypertreeLayers poly257MultiLeafSuite multiLeaf4JortsParams sk pk.pkRoot rRand
          q.grindLimit 0 q.epoch mu 1 := by
      rw [signProductionHypertreeLayers_succ, signProductionHypertreeLayers_succ]
      simp only [multiLeaf4JortsParams.public_eqs, ↓reduceIte]
      have hGrind : ∀ c rem : Nat,
          grindTswLeafCounterAux symMerkleSuite 4 128 192 rRand sk.pkSeed pk.pkRoot mu 0
            (UInt32.ofNat (q.epoch % 4)) c rem =
          grindTswLeafCounterAux poly257MultiLeafSuite 4 128 192 rRand sk.pkSeed pk.pkRoot mu 0
            (UInt32.ofNat (q.epoch % 4)) c rem := by
        intro c rem; induction rem generalizing c with
        | zero => rw [grindTswLeafCounterAux_zero, grindTswLeafCounterAux_zero]
        | succ rem' ih =>
          rw [grindTswLeafCounterAux_succ, grindTswLeafCounterAux_succ]
          have hHm : ∀ ctr, thHashLeafMsg symMerkleSuite rRand sk.pkSeed pk.pkRoot mu 0
              (UInt32.ofNat (q.epoch % 4)) ctr =
              thHashLeafMsg poly257MultiLeafSuite rRand sk.pkSeed pk.pkRoot mu 0
                (UInt32.ofNat (q.epoch % 4)) ctr := by
            intro ctr; rw [thHashLeafMsg_eq, thHashLeafMsg_eq]
            exact symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.1
          rw [hHm, ih (c + 1)]
      rw [hGrind]
      cases grindTswLeafCounterAux poly257MultiLeafSuite 4 128 192 rRand sk.pkSeed pk.pkRoot mu 0
          (UInt32.ofNat (q.epoch % 4)) 0 q.grindLimit with
      | none => rfl
      | some triple =>
        rcases triple with ⟨ctr, digits, _⟩
        dsimp only
        rw [signProductionHypertreeLayers_zero, signProductionHypertreeLayers_zero]
        dsimp only
        have hChainsEq :
            ((List.range 128).map fun r =>
              wotsChainSteps symMerkleSuite sk.pkSeed 0 0 (q.epoch % 4) r 0 (digits.getD r 0)
                (wotsSecretBase symMerkleSuite sk 0 0 (q.epoch % 4) r)) =
            ((List.range 128).map fun r =>
              wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 (q.epoch % 4) r 0 (digits.getD r 0)
                (wotsSecretBase poly257MultiLeafSuite sk 0 0 (q.epoch % 4) r)) := by
          apply List.map_congr_left
          intro r _
          have hSec : wotsSecretBase symMerkleSuite sk 0 0 (q.epoch % 4) r =
              wotsSecretBase poly257MultiLeafSuite sk 0 0 (q.epoch % 4) r := by
            rw [wotsSecretBase_eq, wotsSecretBase_eq, thSecretPrf_eq, thSecretPrf_eq]
            exact symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.1
          have hSt : ∀ (k s : Nat) (x : List UInt8),
              wotsChainSteps symMerkleSuite sk.pkSeed 0 0 (q.epoch % 4) r s k x =
                wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 (q.epoch % 4) r s k x := by
            intro k; induction k with
            | zero => intro s x; rw [wotsChainSteps_zero, wotsChainSteps_zero]
            | succ k' ih =>
              intro s x; rw [wotsChainSteps_succ, wotsChainSteps_succ]; dsimp only
              rw [thChainF_eq, thChainF_eq,
                symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.2.1]
              exact ih (s + 1) _
          rw [hSec, hSt]
        have hPathEq0 :
            buildMerkleAuthPathKp symMerkleSuite sk.pkSeed 0 0 .tree 0
              (computeWotsPk symMerkleSuite multiLeaf4JortsParams sk 0 0) 2 0 0 (q.epoch % 4) =
            buildMerkleAuthPathKp poly257MultiLeafSuite sk.pkSeed 0 0 .tree 0
              (computeWotsPk poly257MultiLeafSuite multiLeaf4JortsParams sk 0 0) 2 0 0
              (q.epoch % 4) := by
          have hMod : q.epoch % 4 = q.epoch := Nat.mod_eq_of_lt hEpLt
          rw [hMod, symMerkleSuite_authPath_eq sk hEpLt]
          have hValid0 := prodSignQuery_poly257MultiLeaf_valid sk hEpLt (by decide : 0 < 3)
            Nat.one_pos []
          rw [prodSignQuery_eq] at hValid0
          simp only [multiLeaf4JortsParams.public_eqs, ↓reduceIte] at hValid0
          rw [evalProductionStatefulSign_eq] at hValid0
          have hNotOut0 : (!true || !decide (q.epoch < 2 ^ 2)) = false := by simp [hEpLt]
          simp only [multiLeaf4JortsParams.public_eqs,
            PqHashParams.productionWellFormed.public_eqs,
            PqHashParams.productionLeafIdxInRange.public_eqs, hNotOut0, Bool.false_eq_true,
            ↓reduceIte] at hValid0
          dsimp only at hValid0
          rw [signProductionHypertreeCore_def] at hValid0
          simp only [multiLeaf4JortsParams.public_eqs, ↓reduceIte] at hValid0
          rw [signProductionHypertreeLayers_succ] at hValid0
          dsimp only at hValid0
          cases hG0 : grindTswLeafCounterAux poly257MultiLeafSuite 4 128
              { w := 4, ell1 := 128, subtreeHeight := 2, numLayers := 1, forsTrees := 0,
                forsHeight := 0, maxSigsLog2 := 2, statefulJorts := true }.targetSum _ _ _ _ 0
              (UInt32.ofNat (q.epoch % 4)) 0 1 with
          | none => rw [hG0] at hValid0; cases hValid0
          | some t0 =>
            rcases t0 with ⟨_, _, _⟩
            rw [hG0, signProductionHypertreeLayers_zero] at hValid0
            dsimp only at hValid0
            split at hValid0
            · rw [honestMultiLeafSig.public_eqs] at hValid0
              injection hValid0 with hSigEq
              have hLayerEq := congrArg PqHashSig.layerSigs hSigEq
              injection hLayerEq with hHeadEq _
              have hPathEq := congrArg LayerXmssSig.authPath hHeadEq
              dsimp only at hPathEq
              rw [hMod] at hPathEq
              exact hPathEq.symm
            · cases hValid0
        rw [hChainsEq, hPathEq0]
    cases hPolyL : signProductionHypertreeLayers poly257MultiLeafSuite multiLeaf4JortsParams sk
        pk.pkRoot rRand q.grindLimit 0 q.epoch mu 1 with
    | none => rw [hLayersEq, hPolyL]
    | some layerSigs =>
      have hSymL : signProductionHypertreeLayers symMerkleSuite multiLeaf4JortsParams sk pk.pkRoot
          rRand q.grindLimit 0 q.epoch mu 1 = some layerSigs := hLayersEq.trans hPolyL
      rw [hSymL, hPolyL]
      dsimp only
      have hEpBound : q.epoch < 2 ^ (1 * multiLeaf4JortsParams.subtreeHeight) := by
        simpa [multiLeaf4JortsParams.public_eqs] using hEpLt
      obtain ⟨hLenS, hVerSymL⟩ := signProductionHypertreeLayers_sound symMerkleSuite
        multiLeaf4JortsParams sk pk.pkRoot rRand q.grindLimit 1 0 q.epoch mu layerSigs
        Nat.one_pos hEpBound hSymL
      obtain ⟨_, hVerPolyL⟩ := signProductionHypertreeLayers_sound poly257MultiLeafSuite
        multiLeaf4JortsParams sk pk.pkRoot rRand q.grindLimit 1 0 q.epoch mu layerSigs
        Nat.one_pos hEpBound hPolyL
      have hPkSeed : pk.pkSeed = sk.pkSeed := by unfold pk derivePublicKey; rfl
      have hPkRootPoly : computeXmssSubtreeRoot poly257MultiLeafSuite multiLeaf4JortsParams sk 0 0 =
          pk.pkRoot := by unfold pk derivePublicKey; rfl
      have hPkRootSym : computeXmssSubtreeRoot symMerkleSuite multiLeaf4JortsParams sk 0 0 =
          pk.pkRoot := by rw [symMerkleSuite_subtreeRoot, ← hPkRootPoly]; exact
            (by rw [← symMerkleSuite_derivePublicKey]; unfold derivePublicKey; exact symMerkleSuite_subtreeRoot sk).symm.trans
              (by rw [symMerkleSuite_derivePublicKey]; unfold pk; rfl)
      have hVer1 : verifyProductionPqHashSig symMerkleSuite multiLeaf4JortsParams pk q.message
          ⟨rRand, 0, q.epoch, [], layerSigs⟩ = true := by
        rw [verifyProductionPqHashSig_eq, ite_eq_right hNotOut]
        have hShape : ¬ (layerSigs.length ≠ multiLeaf4JortsParams.numLayers || (0 : Nat) ≠ 0) := by
          simp [hLenS, multiLeaf4JortsParams.public_eqs]
        rw [ite_eq_right hShape]
        simp only [hStTrue, ↓reduceIte, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true]
        have hMuSym : thPreHash symMerkleSuite pk.pkSeed pk.pkRoot q.message = mu := by
          rw [hPkSeed]; exact hPre q.message
        rw [hMuSym, hPkSeed, hVerSymL, show UInt32.ofNat (0 + 1 - 1) = 0 from rfl, hPkRootSym]
        exact decide_eq_true rfl
      have hVer2 : verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams pk
          q.message ⟨rRand, 0, q.epoch, [], layerSigs⟩ = true := by
        rw [verifyProductionPqHashSig_eq, ite_eq_right hNotOut]
        have hShape : ¬ (layerSigs.length ≠ multiLeaf4JortsParams.numLayers || (0 : Nat) ≠ 0) := by
          simp [hLenS, multiLeaf4JortsParams.public_eqs]
        rw [ite_eq_right hShape]
        simp only [hStTrue, ↓reduceIte, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true]
        change (match verifyProductionHypertreeLayers poly257MultiLeafSuite multiLeaf4JortsParams
          pk.pkSeed pk.pkRoot rRand 0 q.epoch mu layerSigs with | _ => _) = true
        rw [hPkSeed, hVerPolyL, show UInt32.ofNat (0 + 1 - 1) = 0 from rfl, hPkRootPoly]
        exact decide_eq_true rfl
      rw [hVer1, hVer2]

private theorem symMerkleSuite_h2_d1_left_right (pkSeed nL nR : List UInt8) (sk : PqSecretKey)
    (hEq : thNodeH symMerkleSuite pkSeed ⟨0, 0, .tree, 0, 2, 0⟩ nL nR =
      rootFromTbl (honestSlotHiLo sk)) :
    nL.headD 0 = 0xD1 ∧ nR.headD 0 = 0xD1 ∧
    (nL.drop 2).take 12 =
      packLeaf3 [honestSlotHiLo sk 0 0, honestSlotHiLo sk 0 1, honestSlotHiLo sk 0 2] ++
      packLeaf3 [honestSlotHiLo sk 1 0, honestSlotHiLo sk 1 1, honestSlotHiLo sk 1 2] ∧
    (nR.drop 2).take 12 =
      packLeaf3 [honestSlotHiLo sk 2 0, honestSlotHiLo sk 2 1, honestSlotHiLo sk 2 2] ++
      packLeaf3 [honestSlotHiLo sk 3 0, honestSlotHiLo sk 3 1, honestSlotHiLo sk 3 2] := by
  rw [thNodeH_eq, thCall_eq] at hEq
  unfold symMerkleSuite at hEq; dsimp only at hEq
  rw [parseThPreimage_thPreimage] at hEq; dsimp only at hEq
  rw [ite_eq_left rfl] at hEq
  have hc2 : (2 : UInt32).toNat = 2 := rfl
  have hs0 : (0 : UInt32).toNat = 0 := rfl
  simp only [hc2, hs0, (by decide : ¬ (2 = 1 ∧ 0 < 2)), and_self, ↓reduceIte] at hEq
  split at hEq
  · rename_i hc
    have hdL : nL.headD 0 = 0xD1 := by
      cases nL with
      | nil => cases hc.1
      | cons b _ => injection hc.1 with hb _; exact hb
    have hdR : nR.headD 0 = 0xD1 := by
      cases nR with
      | nil => cases hc.2.2.2.1
      | cons b _ => injection hc.2.2.2.1 with hb _; exact hb
    have hLenL : ((nL.drop 2).take 12).length = 12 := by
      rw [List.length_take, List.length_drop, hc.2.2.1]; decide
    have hLenR : ((nR.drop 2).take 12).length = 12 := by
      rw [List.length_take, List.length_drop, hc.2.2.2.2.2]; decide
    rw [rootFromTbl.public_eqs] at hEq
    have hP0 : (packLeaf3 [honestSlotHiLo sk 0 0, honestSlotHiLo sk 0 1, honestSlotHiLo sk 0 2] ++
        packLeaf3 [honestSlotHiLo sk 1 0, honestSlotHiLo sk 1 1, honestSlotHiLo sk 1 2]).length =
        12 := by rw [packLeaf3.public_eqs, packLeaf3.public_eqs]; rfl
    have hP1 : (packLeaf3 [honestSlotHiLo sk 2 0, honestSlotHiLo sk 2 1, honestSlotHiLo sk 2 2] ++
        packLeaf3 [honestSlotHiLo sk 3 0, honestSlotHiLo sk 3 1, honestSlotHiLo sk 3 2]).length =
        12 := by rw [packLeaf3.public_eqs, packLeaf3.public_eqs]; rfl
    have hAssocL : ([0xD2, 0] ++ (nL.drop 2).take 12 ++ (nR.drop 2).take 12 ++
        List.replicate 6 0x00).drop 2 =
        (nL.drop 2).take 12 ++ ((nR.drop 2).take 12 ++ List.replicate 6 0x00) := by
      simp [List.append_assoc]
    have hAssocR : ([0xD2, 0] ++
        packLeaf3 [honestSlotHiLo sk 0 0, honestSlotHiLo sk 0 1, honestSlotHiLo sk 0 2] ++
        packLeaf3 [honestSlotHiLo sk 1 0, honestSlotHiLo sk 1 1, honestSlotHiLo sk 1 2] ++
        packLeaf3 [honestSlotHiLo sk 2 0, honestSlotHiLo sk 2 1, honestSlotHiLo sk 2 2] ++
        packLeaf3 [honestSlotHiLo sk 3 0, honestSlotHiLo sk 3 1, honestSlotHiLo sk 3 2] ++
        List.replicate 6 0x00).drop 2 =
        (packLeaf3 [honestSlotHiLo sk 0 0, honestSlotHiLo sk 0 1, honestSlotHiLo sk 0 2] ++
         packLeaf3 [honestSlotHiLo sk 1 0, honestSlotHiLo sk 1 1, honestSlotHiLo sk 1 2]) ++
        ((packLeaf3 [honestSlotHiLo sk 2 0, honestSlotHiLo sk 2 1, honestSlotHiLo sk 2 2] ++
          packLeaf3 [honestSlotHiLo sk 3 0, honestSlotHiLo sk 3 1, honestSlotHiLo sk 3 2]) ++
         List.replicate 6 0x00) := by
      simp [List.append_assoc]
    have hDrop2Eq := congrArg (List.drop 2) hEq
    rw [hAssocL, hAssocR] at hDrop2Eq
    have hTake12 := congrArg (List.take 12) hDrop2Eq
    rw [List.take_left' hLenL, List.take_left' hP0] at hTake12
    have hDrop12 := congrArg (List.drop 12) hDrop2Eq
    rw [List.drop_left' hLenL, List.drop_left' hP0] at hDrop12
    have hTake12R := congrArg (List.take 12) hDrop12
    rw [List.take_left' hLenR, List.take_left' hP1] at hTake12R
    exact ⟨hdL, hdR, hTake12, hTake12R⟩
  · have hHead := congrArg (fun l => l.headD 0) hEq
    rw [rootFromTbl.public_eqs] at hHead
    cases hHead

private theorem symMerkleSuite_h1_d1_children (pkSeed a b : List UInt8) (idx : Nat)
    (hIdx : idx < 2)
    (hHd : (thNodeH symMerkleSuite pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat idx⟩ a b).headD 0 =
      0xD1) :
    a.headD 0 = 0xC0 ∧ b.headD 0 = 0xC0 ∧
    ((a.drop 2).take 6).length = 6 ∧
    ((thNodeH symMerkleSuite pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat idx⟩ a b).drop 2).take 12 =
      (a.drop 2).take 6 ++ (b.drop 2).take 6 := by
  rw [thNodeH_eq, thCall_eq] at hHd ⊢
  unfold symMerkleSuite at hHd ⊢; dsimp only at hHd ⊢
  rw [parseThPreimage_thPreimage] at hHd ⊢; dsimp only at hHd ⊢
  rw [ite_eq_left rfl] at hHd ⊢
  have hIdx32 : (UInt32.ofNat idx).toNat = idx := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hc1 : (1 : UInt32).toNat = 1 := rfl
  simp only [hc1, hIdx32, hIdx, and_self, ↓reduceIte] at hHd ⊢
  split at hHd
  · rename_i hc
    rw [ite_eq_left hc]
    have hLA : ((a.drop 2).take 6).length = 6 := by
      rw [List.length_take, List.length_drop, hc.2.2.1]; decide
    have hLB : ((b.drop 2).take 6).length = 6 := by
      rw [List.length_take, List.length_drop, hc.2.2.2.2.2]; decide
    have hSum12 : ((a.drop 2).take 6 ++ (b.drop 2).take 6).length = 12 := by
      rw [List.length_append, hLA, hLB]
    have hDr : ([0xD1, UInt8.ofNat idx] ++ (a.drop 2).take 6 ++ (b.drop 2).take 6 ++
        List.replicate 18 0x00).drop 2 =
        ((a.drop 2).take 6 ++ (b.drop 2).take 6) ++ List.replicate 18 0x00 := by
      simp [List.append_assoc]
    rw [hDr, List.take_left' hSum12]
    exact ⟨hc.1, hc.2.2.2.1, hLA, rfl⟩
  · cases hHd

private theorem symMerkleSuite_walk_pins_wotsPk (pkSeed : List UInt8) (sk : PqSecretKey)
    {kp : Nat} (hkp : kp < 4) {limbs : List (List UInt8)}
    {path : List (List UInt8)}
    (hWalk : walkMerkleAuthPathKp symMerkleSuite pkSeed 0 0 .tree 0 2 0 kp
      (thTweakTl poly257MultiLeafSuite pkSeed ⟨0, 0, .wotsPk, UInt32.ofNat kp, 0, 0⟩ limbs) path =
      some (rootFromTbl (honestSlotHiLo sk))) :
    thTweakTl poly257MultiLeafSuite pkSeed ⟨0, 0, .wotsPk, UInt32.ofNat kp, 0, 0⟩ limbs =
      leafFromTbl (honestSlotHiLo sk) kp := by
  let wPk := thTweakTl poly257MultiLeafSuite pkSeed ⟨0, 0, .wotsPk, UInt32.ofNat kp, 0, 0⟩ limbs
  change walkMerkleAuthPathKp symMerkleSuite pkSeed 0 0 .tree 0 2 0 kp wPk path = _ at hWalk
  match path with
  | [] | [_] | _ :: _ :: _ :: _ =>
    have hCases : kp = 0 ∨ kp = 1 ∨ kp = 2 ∨ kp = 3 := by omega
    rcases hCases with rfl | rfl | rfl | rfl <;>
      (unfold walkMerkleAuthPathKp at hWalk; simp at hWalk;
       try (unfold walkMerkleAuthPathKp at hWalk; simp at hWalk);
       try (unfold walkMerkleAuthPathKp at hWalk; simp at hWalk))
  | [sib1, sib0] =>
    have hHeadAndSlice : wPk.headD 0 = 0xC0 ∧
        (wPk.drop 2).take 6 =
          packLeaf3 [honestSlotHiLo sk kp 0, honestSlotHiLo sk kp 1, honestSlotHiLo sk kp 2] := by
      have hL6b : ∀ j, (packLeaf3 [honestSlotHiLo sk j 0, honestSlotHiLo sk j 1,
          honestSlotHiLo sk j 2]).length = 6 := fun _ => by rw [packLeaf3.public_eqs]; rfl
      have hSubH : ∀ (idx : Nat) (x y : List UInt8), idx < 2 →
          (thNodeH symMerkleSuite pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat idx⟩ x y).headD 0 =
            0xD1 →
          ((thNodeH symMerkleSuite pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat idx⟩ x y).drop 2).take
              12 =
            packLeaf3 [honestSlotHiLo sk (2 * idx) 0, honestSlotHiLo sk (2 * idx) 1,
              honestSlotHiLo sk (2 * idx) 2] ++
            packLeaf3 [honestSlotHiLo sk (2 * idx + 1) 0, honestSlotHiLo sk (2 * idx + 1) 1,
              honestSlotHiLo sk (2 * idx + 1) 2] →
          (x.headD 0 = 0xC0 ∧ (x.drop 2).take 6 = packLeaf3
            [honestSlotHiLo sk (2 * idx) 0, honestSlotHiLo sk (2 * idx) 1,
              honestSlotHiLo sk (2 * idx) 2]) ∧
          (y.headD 0 = 0xC0 ∧ (y.drop 2).take 6 = packLeaf3
            [honestSlotHiLo sk (2 * idx + 1) 0, honestSlotHiLo sk (2 * idx + 1) 1,
              honestSlotHiLo sk (2 * idx + 1) 2]) := by
        intro idx x y hIdx hd hEq12
        obtain ⟨hx0, hy0, hLx, hSl⟩ := symMerkleSuite_h1_d1_children _ x y idx hIdx hd
        rw [hSl] at hEq12
        have hTk := congrArg (List.take 6) hEq12
        have hDr := congrArg (List.drop 6) hEq12
        rw [List.take_left' hLx, List.take_left' (hL6b (2 * idx))] at hTk
        rw [List.drop_left' hLx, List.drop_left' (hL6b (2 * idx))] at hDr
        exact ⟨⟨hx0, hTk⟩, ⟨hy0, hDr⟩⟩
      have hCases : kp = 0 ∨ kp = 1 ∨ kp = 2 ∨ kp = 3 := by omega
      rcases hCases with rfl | rfl | rfl | rfl
      · unfold walkMerkleAuthPathKp at hWalk; simp only [(by decide : 0 < 2 ^ 1), ↓reduceIte] at hWalk
        unfold walkMerkleAuthPathKp at hWalk; simp only [(by decide : 0 < 2 ^ 0), ↓reduceIte] at hWalk
        unfold walkMerkleAuthPathKp at hWalk; injection hWalk with hRootEq
        obtain ⟨hdL, _, hSL, _⟩ := symMerkleSuite_h2_d1_left_right _ _ _ sk hRootEq
        exact (hSubH 0 _ _ (by decide) hdL hSL).1
      · unfold walkMerkleAuthPathKp at hWalk; simp only [(by decide : 1 < 2 ^ 1), ↓reduceIte] at hWalk
        unfold walkMerkleAuthPathKp at hWalk; simp only [(by decide : ¬ (1 < 2 ^ 0)), ↓reduceIte] at hWalk
        unfold walkMerkleAuthPathKp at hWalk; injection hWalk with hRootEq
        obtain ⟨hdL, _, hSL, _⟩ := symMerkleSuite_h2_d1_left_right _ _ _ sk hRootEq
        exact (hSubH 0 _ _ (by decide) hdL hSL).2
      · unfold walkMerkleAuthPathKp at hWalk; simp only [(by decide : ¬ (2 < 2 ^ 1)), ↓reduceIte] at hWalk
        unfold walkMerkleAuthPathKp at hWalk; simp only [(by decide : 2 - 2 < 2 ^ 0), ↓reduceIte] at hWalk
        unfold walkMerkleAuthPathKp at hWalk; injection hWalk with hRootEq
        obtain ⟨_, hdR, _, hSR⟩ := symMerkleSuite_h2_d1_left_right _ _ _ sk hRootEq
        exact (hSubH 1 _ _ (by decide) hdR hSR).1
      · unfold walkMerkleAuthPathKp at hWalk; simp only [(by decide : ¬ (3 < 2 ^ 1)), ↓reduceIte] at hWalk
        unfold walkMerkleAuthPathKp at hWalk; simp only [(by decide : ¬ (3 - 2 < 2 ^ 0)), ↓reduceIte] at hWalk
        unfold walkMerkleAuthPathKp at hWalk; injection hWalk with hRootEq
        obtain ⟨_, hdR, _, hSR⟩ := symMerkleSuite_h2_d1_left_right _ _ _ sk hRootEq
        exact (hSubH 1 _ _ (by decide) hdR hSR).2
    rcases poly257MultiLeaf_thTweakTl_cases pkSeed hkp limbs with ⟨ps, hPsEq⟩ | hFF
    · change wPk = _ at hPsEq ⊢
      have hSlicePs : (wPk.drop 2).take 6 = packLeaf3 ps := by
        rw [hPsEq, packLeaf3.public_eqs]; rfl
      rw [hPsEq, ← hSlicePs, hHeadAndSlice.2, leafFromTbl.public_eqs]
    · change wPk = _ at hFF
      rw [hFF] at hHeadAndSlice
      cases hHeadAndSlice.1

private def canonicalizeSymSigFromPk (pkRoot : List UInt8) (sig : PqHashSig) : PqHashSig :=
  let tblFromPk : Nat → Nat → UInt8 × UInt8 := fun kp r =>
    let base := 2 + 6 * kp + 2 * r
    (pkRoot.getD base 0, pkRoot.getD (base + 1) 0)
  match sig.layerSigs with
  | [lsig] =>
    { sig with layerSigs := [⟨lsig.tswCtr, lsig.wotsChains,
        authPathFromTbl tblFromPk sig.leafGlobalIdx⟩] }
  | _ => sig

private theorem tblFromPkRoot_eq_honest (sk : PqSecretKey) {kp r : Nat} (hkp : kp < 4) (hr : r < 3) :
    let pkRoot := rootFromTbl (honestSlotHiLo sk)
    let base := 2 + 6 * kp + 2 * r
    (pkRoot.getD base 0, pkRoot.getD (base + 1) 0) = honestSlotHiLo sk kp r := by
  rw [rootFromTbl.public_eqs, packLeaf3.public_eqs, packLeaf3.public_eqs,
    packLeaf3.public_eqs, packLeaf3.public_eqs]
  have hCasesKp : kp = 0 ∨ kp = 1 ∨ kp = 2 ∨ kp = 3 := by omega
  have hCasesR : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hCasesKp with rfl | rfl | rfl | rfl <;>
    rcases hCasesR with rfl | rfl | rfl <;> rfl

private def mapTreePost {α β : Type} (f : α → β) :
    ProdAdaptiveTree α → ProdAdaptiveTree β
  | .pure ret => .pure (f ret)
  | .hashQuery x next => .hashQuery x (fun y => mapTreePost f (next y))
  | .signQuery q next => .signQuery q (fun resp => mapTreePost f (next resp))

private theorem mapTreePost_bounded {α β : Type} (f : α → β) :
    ∀ {qH qS : Nat} (prog : ProdAdaptiveTree α),
      ProdDualBounded qH qS prog → ProdDualBounded qH qS (mapTreePost f prog)
  | _, _, .pure _, _ => trivial
  | 0, _, .hashQuery _ _, h => False.elim h
  | _ + 1, _, .hashQuery _ next, h => fun y => mapTreePost_bounded f (next y) (h y)
  | _, 0, .signQuery _ _, h => False.elim h
  | _, _ + 1, .signQuery _ next, h => fun resp => mapTreePost_bounded f (next resp) (h resp)

private theorem evalLatched_mapTreePost {α β : Type} (f : α → β)
    (raw : List UInt8 → List UInt8) (sign : ProdSigningQuery → Option PqHashSig) :
    ∀ (prog : ProdAdaptiveTree α) (lo : Nat),
      evalLatchedAdaptiveTree true raw sign (mapTreePost f prog) lo =
        (f (evalLatchedAdaptiveTree true raw sign prog lo).1,
         (evalLatchedAdaptiveTree true raw sign prog lo).2)
  | .pure _, _ => by simp only [mapTreePost, evalLatchedAdaptiveTree.public_eqs]
  | .hashQuery x next, lo => by
    unfold mapTreePost
    rw [evalLatchedAdaptiveTree.public_eq_2, evalLatchedAdaptiveTree.public_eq_2]
    exact evalLatched_mapTreePost f raw sign (next (raw x)) lo
  | .signQuery q next, lo => by
    unfold mapTreePost
    rw [evalLatchedAdaptiveTree_sign, evalLatchedAdaptiveTree_sign]
    by_cases hLo : lo ≤ q.epoch
    · rw [ite_eq_left (Or.inr hLo), ite_eq_left (Or.inr hLo),
        evalLatched_mapTreePost f raw sign (next (sign q)) (q.epoch + 1)]
    · have hNot : ¬ ((true = false) ∨ lo ≤ q.epoch) := fun hOr =>
        hOr.elim (fun hb => Bool.noConfusion hb) hLo
      rw [ite_eq_right hNot, ite_eq_right hNot]
      exact evalLatched_mapTreePost f raw sign (next none) lo

