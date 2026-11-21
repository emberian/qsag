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
  rawHash_len raw := by split <;> exact suite.rawHash_len _

theorem zeroKpLayerOfSuite_thCall (suite : TweakableHashSuite)
    (role pkSeed : List UInt8) (adrs : HashAdrs) (args : List (List UInt8)) :
    thCall (zeroKpLayerOfSuite suite) role pkSeed adrs args =
      thCall suite role pkSeed { adrs with layer := 0, keyPair := 0 } args := by
  rw [thCall_eq, thCall_eq]; unfold zeroKpLayerOfSuite; dsimp only; rw [parseThPreimage_thPreimage]

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
    cases parseThPreimage raw with
    | none => exact poly257MultiLeafSuite.rawHash_len raw
    | some q =>
      rcases q with ⟨role, _, adrs, args⟩; dsimp only; split
      · cases args with
        | nil => rfl
        | cons left t1 =>
          cases t1 with
          | nil => rfl
          | cons right t2 =>
            cases t2 with
            | cons _ _ => rfl
            | nil =>
              dsimp only; split
              · split
                · split
                  · rename_i hc
                    have hL : ((left.drop 2).take 6).length = 6 := by
                      rw [List.length_take, List.length_drop, hc.2.2.1]; decide
                    have hR : ((right.drop 2).take 6).length = 6 := by
                      rw [List.length_take, List.length_drop, hc.2.2.2.2.2]; decide
                    rw [List.length_append, List.length_append, List.length_append,
                      hL, hR, List.length_replicate]; rfl
                  · rfl
                · split
                  · split
                    · rename_i hc
                      have hL : ((left.drop 2).take 12).length = 12 := by
                        rw [List.length_take, List.length_drop, hc.2.2.1]; decide
                      have hR : ((right.drop 2).take 12).length = 12 := by
                        rw [List.length_take, List.length_drop, hc.2.2.2.2.2]; decide
                      rw [List.length_append, List.length_append, List.length_append,
                        hL, hR, List.length_replicate]; rfl
                    · rfl
                  · rfl
              · rfl
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
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hIdx (by decide))]
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
    (leafFromTbl tbl kp).headD 0 = 0xC0 ∧ (leafFromTbl tbl kp).drop 8 = List.replicate 24 0x00 ∧
    (leafFromTbl tbl kp).length = 32 ∧
    ((leafFromTbl tbl kp).drop 2).take 6 = packLeaf3 [tbl kp 0, tbl kp 1, tbl kp 2] := by
  rw [leafFromTbl.public_eqs, packLeaf3.public_eqs]; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem node1FromTbl_shape (tbl : Nat → Nat → UInt8 × UInt8) (idx : Nat) :
    (node1FromTbl tbl idx).take 2 = [0xD1, UInt8.ofNat idx] ∧
    (node1FromTbl tbl idx).drop 14 = List.replicate 18 0x00 ∧ (node1FromTbl tbl idx).length = 32 ∧
    ((node1FromTbl tbl idx).drop 2).take 12 =
      packLeaf3 [tbl (2 * idx) 0, tbl (2 * idx) 1, tbl (2 * idx) 2] ++
      packLeaf3 [tbl (2 * idx + 1) 0, tbl (2 * idx + 1) 1, tbl (2 * idx + 1) 2] := by
  rw [node1FromTbl.public_eqs, packLeaf3.public_eqs, packLeaf3.public_eqs]; exact ⟨rfl, rfl, rfl, rfl⟩

private theorem symMerkleSuite_subtreeRoot (sk : PqSecretKey) :
    computeXmssSubtreeRoot symMerkleSuite multiLeaf4JortsParams sk 0 0 =
      rootFromTbl (honestSlotHiLo sk) := by
  rw [computeXmssSubtreeRoot_eq]
  have hSubH : multiLeaf4JortsParams.subtreeHeight = 2 := by rw [multiLeaf4JortsParams.public_eqs]
  have hc1 : UInt32.ofNat (0 + 1) = 1 := rfl; have hc2 : UInt32.ofNat (1 + 1) = 2 := rfl
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
  have hN0Eq : thNodeH symMerkleSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, 0⟩
      (leafFromTbl (honestSlotHiLo sk) 0) (leafFromTbl (honestSlotHiLo sk) 1) =
      node1FromTbl (honestSlotHiLo sk) 0 := by
    change thNodeH symMerkleSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat 0⟩ _ _ = _
    rw [symMerkleSuite_thNodeH_h1 sk.pkSeed 0 0 _ _ (by decide) ⟨hL0.1, hL0.2.1, hL0.2.2.1⟩
      ⟨hL1.1, hL1.2.1, hL1.2.2.1⟩, hL0.2.2.2, hL1.2.2.2, node1FromTbl.public_eqs]
  have hN1Eq : thNodeH symMerkleSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, 1⟩
      (leafFromTbl (honestSlotHiLo sk) 2) (leafFromTbl (honestSlotHiLo sk) 3) =
      node1FromTbl (honestSlotHiLo sk) 1 := by
    change thNodeH symMerkleSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat 1⟩ _ _ = _
    rw [symMerkleSuite_thNodeH_h1 sk.pkSeed 0 1 _ _ (by decide) ⟨hL2.1, hL2.2.1, hL2.2.2.1⟩
      ⟨hL3.1, hL3.2.1, hL3.2.2.1⟩, hL2.2.2.2, hL3.2.2.2, node1FromTbl.public_eqs]
  rw [hN0Eq, hN1Eq]
  have hM0 := node1FromTbl_shape (honestSlotHiLo sk) 0
  have hM1 := node1FromTbl_shape (honestSlotHiLo sk) 1
  rw [symMerkleSuite_thNodeH_h2 sk.pkSeed 0 _ _ ⟨hM0.1, hM0.2.1, hM0.2.2.1⟩
    ⟨hM1.1, hM1.2.1, hM1.2.2.1⟩, hM0.2.2.2, hM1.2.2.2, rootFromTbl.public_eqs]
  simp only [List.append_assoc]

private theorem symMerkleSuite_derivePublicKey (sk : PqSecretKey) :
    derivePublicKey symMerkleSuite multiLeaf4JortsParams sk =
      derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk := by
  rw [derivePublicKey_poly257MultiLeaf, pkFromTbl.public_eqs]; unfold derivePublicKey
  have hTop : UInt32.ofNat (multiLeaf4JortsParams.numLayers - 1) = 0 := by
    rw [multiLeaf4JortsParams.public_eqs]; rfl
  rw [hTop]; dsimp only; rw [symMerkleSuite_subtreeRoot]

private theorem lt4_cases {n : Nat} (h : n < 4) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 :=
  match n with
  | 0 => .inl rfl | 1 => .inr (.inl rfl) | 2 => .inr (.inr (.inl rfl)) | 3 => .inr (.inr (.inr rfl))
  | _ + 4 => False.elim (Nat.not_lt_zero _ (Nat.lt_of_add_lt_add_right h))

private theorem lt3_cases {n : Nat} (h : n < 3) : n = 0 ∨ n = 1 ∨ n = 2 :=
  match n with
  | 0 => .inl rfl | 1 => .inr (.inl rfl) | 2 => .inr (.inr rfl)
  | _ + 3 => False.elim (Nat.not_lt_zero _ (Nat.lt_of_add_lt_add_right h))

private theorem symMerkleSuite_authPath_eq (sk : PqSecretKey) {kp : Nat} (hkp : kp < 4) :
    buildMerkleAuthPathKp symMerkleSuite sk.pkSeed 0 0 .tree 0
      (computeWotsPk symMerkleSuite multiLeaf4JortsParams sk 0 0) 2 0 0 kp =
      authPathFromTbl (honestSlotHiLo sk) kp := by
  have hCases := lt4_cases hkp
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
      hL0.2.2.2, hL1.2.2.2, node1FromTbl.public_eqs]
  have hN1Eq : thNodeH symMerkleSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat 1⟩
      (leafFromTbl (honestSlotHiLo sk) 2) (leafFromTbl (honestSlotHiLo sk) 3) =
      node1FromTbl (honestSlotHiLo sk) 1 := by
    rw [symMerkleSuite_thNodeH_h1 sk.pkSeed 0 1 _ _ (by decide)
      ⟨hL2.1, hL2.2.1, hL2.2.2.1⟩ ⟨hL3.1, hL3.2.1, hL3.2.2.1⟩,
      hL2.2.2.2, hL3.2.2.2, node1FromTbl.public_eqs]
  rcases hCases with rfl | rfl | rfl | rfl <;>
    (rw [buildMerkleAuthPathKp.public_eq_2]; dsimp only;
     simp only [(by decide : 0 < 2 ^ 1), (by decide : 1 < 2 ^ 1),
       (by decide : ¬ (2 < 2 ^ 1)), (by decide : ¬ (3 < 2 ^ 1)), ↓reduceIte];
     rw [buildMerkleAuthPathKp.public_eq_2]; dsimp only;
     simp only [(by decide : 0 < 2 ^ 0), (by decide : ¬ (1 < 2 ^ 0)), ↓reduceIte];
     rw [buildMerkleAuthPathKp.public_eq_1, computeMerkleNodeKp_succ, computeMerkleNodeKp_zero,
       computeMerkleNodeKp_zero, computeMerkleNodeKp_zero, hc1,
       symMerkleSuite_computeWotsPk_eq, symMerkleSuite_computeWotsPk_eq,
       symMerkleSuite_computeWotsPk_eq];
     try rw [poly257MultiLeaf_computeWotsPk_eq sk (by decide : 0 < 4)];
     try rw [poly257MultiLeaf_computeWotsPk_eq sk (by decide : 1 < 4)];
     try rw [poly257MultiLeaf_computeWotsPk_eq sk (by decide : 2 < 4)];
     try rw [poly257MultiLeaf_computeWotsPk_eq sk (by decide : 3 < 4)];
     rw [show (0 : UInt32) = UInt32.ofNat 0 from rfl,
         show (1 : UInt32) = UInt32.ofNat 1 from rfl] at *;
     first | (rw [hN1Eq, authPathFromTbl.public_eqs]; rfl)
           | (rw [hN0Eq, authPathFromTbl.public_eqs]; rfl))

private theorem multiLeaf4Jorts_leafIdxInRange (ep : Nat) :
    multiLeaf4JortsParams.productionLeafIdxInRange ep = decide (ep < 4) := by
  rw [PqHashParams.productionLeafIdxInRange_eq, multiLeaf4JortsParams.public_eqs]; rfl

private theorem symMerkleSuite_prodSignQuery_eq (sk : PqSecretKey) (q : ProdSigningQuery) :
    prodSignQuery symMerkleSuite multiLeaf4JortsParams sk q =
      prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams sk q := by
  rw [prodSignQuery_eq, prodSignQuery_eq]
  have hSt0 : multiLeaf4JortsParams.statefulJorts = true := by rw [multiLeaf4JortsParams.public_eqs]
  rw [ite_eq_left hSt0, ite_eq_left hSt0, evalProductionStatefulSign_eq, evalProductionStatefulSign_eq]
  have hWf := multiLeaf4JortsParams_productionWellFormed
  if hEpGe : 4 ≤ q.epoch then
    have hRngF : multiLeaf4JortsParams.productionLeafIdxInRange q.epoch = false := by
      rw [multiLeaf4Jorts_leafIdxInRange]; exact decide_eq_false (Nat.not_lt.mpr hEpGe)
    simp only [hSt0, hWf, hRngF, Bool.not_true, Bool.not_false, Bool.false_or, ↓reduceIte]
  else
    have hEpLt : q.epoch < 4 := Nat.lt_of_not_le hEpGe
    have hRngT : multiLeaf4JortsParams.productionLeafIdxInRange q.epoch = true := by
      rw [multiLeaf4Jorts_leafIdxInRange]; exact decide_eq_true hEpLt
    have hNotOut : ¬ ((!multiLeaf4JortsParams.productionWellFormed ||
        !multiLeaf4JortsParams.productionLeafIdxInRange q.epoch) = true) := by
      simp only [hWf, hRngT, Bool.not_true, Bool.or_self, Bool.false_eq_true, not_false_eq_true]
    simp only [hSt0, hWf, hRngT, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    rw [symMerkleSuite_derivePublicKey,
      show (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkSeed = sk.pkSeed from rfl]
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
    let mu := thPreHash poly257MultiLeafSuite sk.pkSeed pk.pkRoot q.message
    let rRand := thPrfMsg poly257MultiLeafSuite sk.skPrf q.randomness mu
    have hStTrue : multiLeaf4JortsParams.statefulJorts = true := by rw [multiLeaf4JortsParams.public_eqs]
    have hNumL : multiLeaf4JortsParams.numLayers = 1 := by rw [multiLeaf4JortsParams.public_eqs]
    simp only [hStTrue, hNumL, ↓reduceIte]
    have hLayersEq :
        signProductionHypertreeLayers symMerkleSuite multiLeaf4JortsParams sk pk.pkRoot rRand
          q.grindLimit 0 q.epoch mu 1 =
        signProductionHypertreeLayers poly257MultiLeafSuite multiLeaf4JortsParams sk pk.pkRoot rRand
          q.grindLimit 0 q.epoch mu 1 := by
      have hDiv0 : q.epoch / 2 ^ 2 = 0 := Nat.div_eq_of_lt hEpLt
      rw [signProductionHypertreeLayers_succ, signProductionHypertreeLayers_succ]
      simp only [multiLeaf4JortsParams.public_eqs]
      rw [hDiv0, show (2 ^ 2 : Nat) = 4 from rfl]
      simp only [decide_true, Bool.and_self, ↓reduceIte, PqHashParams.targetSum_eq,
        show (128 * (4 - 1)) / 2 = 192 from rfl,
        show UInt64.ofNat 0 = (0 : UInt64) from rfl,
        show UInt32.ofNat 0 = (0 : UInt32) from rfl]
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
        rcases triple with ⟨ctr, digits, _⟩; dsimp only
        rw [signProductionHypertreeLayers_zero, signProductionHypertreeLayers_zero]; dsimp only
        have hChainsEq :
            ((List.range 128).map fun r => wotsChainSteps symMerkleSuite sk.pkSeed 0 0 (q.epoch % 4) r 0
              (digits.getD r 0) (wotsSecretBase symMerkleSuite sk 0 0 (q.epoch % 4) r)) =
            ((List.range 128).map fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 (q.epoch % 4) r 0
              (digits.getD r 0) (wotsSecretBase poly257MultiLeafSuite sk 0 0 (q.epoch % 4) r)) := by
          apply List.map_congr_left; intro r _
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
              rw [thChainF_eq, thChainF_eq, symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.2.1]
              exact ih (s + 1) _
          rw [hSec, hSt]
        rw [← multiLeaf4JortsParams.public_eqs]
        have hPathEq0 :
            buildMerkleAuthPathKp symMerkleSuite sk.pkSeed 0 0 .tree 0
              (computeWotsPk symMerkleSuite multiLeaf4JortsParams sk 0 0) 2 0 0 (q.epoch % 4) =
            buildMerkleAuthPathKp poly257MultiLeafSuite sk.pkSeed 0 0 .tree 0
              (computeWotsPk poly257MultiLeafSuite multiLeaf4JortsParams sk 0 0) 2 0 0 (q.epoch % 4) := by
          have hMod : q.epoch % 4 = q.epoch := Nat.mod_eq_of_lt hEpLt
          have hDiv : q.epoch / 4 = 0 := Nat.div_eq_of_lt hEpLt
          rw [hMod, symMerkleSuite_authPath_eq sk hEpLt]
          have hValid0 := prodSignQuery_poly257MultiLeaf_valid sk hEpLt (by decide : 0 < 3) Nat.one_pos []
          rw [prodSignQuery_eq, ite_eq_left hSt0, evalProductionStatefulSign_eq] at hValid0
          simp only [hSt0, hWf, hRngT, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hValid0
          rw [signProductionHypertreeCore_def] at hValid0
          simp only [hSt0, hNumL, ↓reduceIte] at hValid0
          rw [signProductionHypertreeLayers_succ] at hValid0
          simp only [multiLeaf4JortsParams.public_eqs] at hValid0
          rw [hMod, hDiv] at hValid0
          simp only [decide_true, Bool.and_self, ↓reduceIte, PqHashParams.targetSum_eq,
            show (128 * (4 - 1)) / 2 = 192 from rfl,
            show UInt64.ofNat 0 = (0 : UInt64) from rfl,
            show UInt32.ofNat 0 = (0 : UInt32) from rfl] at hValid0
          cases hG0 : grindTswLeafCounterAux poly257MultiLeafSuite 4 128 192 _ _ _ _ 0
              (UInt32.ofNat q.epoch) 0 1 with
          | none => rw [hG0] at hValid0; cases hValid0
          | some t0 =>
            rcases t0 with ⟨_, _, _⟩; rw [hG0, signProductionHypertreeLayers_zero] at hValid0
            dsimp only at hValid0; split at hValid0
            · rw [honestMultiLeafSig.public_eqs] at hValid0; injection hValid0 with hSigEq
              have hLayerEq := congrArg PqHashSig.layerSigs hSigEq; injection hLayerEq with hHeadEq _
              have hPathEq := congrArg LayerXmssSig.authPath hHeadEq; dsimp only at hPathEq
              rw [← multiLeaf4JortsParams.public_eqs] at hPathEq; exact hPathEq.symm
            · cases hValid0
        rw [hChainsEq, hPathEq0]
    cases hPolyL : signProductionHypertreeLayers poly257MultiLeafSuite multiLeaf4JortsParams sk
        pk.pkRoot rRand q.grindLimit 0 q.epoch mu 1 with
    | none =>
      dsimp only [pk, mu, rRand] at hLayersEq hPolyL
      rw [hLayersEq, hPolyL]
    | some layerSigs =>
      have hSymL : signProductionHypertreeLayers symMerkleSuite multiLeaf4JortsParams sk pk.pkRoot
          rRand q.grindLimit 0 q.epoch mu 1 = some layerSigs := hLayersEq.trans hPolyL
      have hSymL' := hSymL
      dsimp only [pk, mu, rRand] at hSymL'
      rw [hSymL']
      dsimp only
      have hEpBound : q.epoch < 2 ^ (1 * multiLeaf4JortsParams.subtreeHeight) := by
        rw [multiLeaf4JortsParams.public_eqs]; exact hEpLt
      obtain ⟨hLenS, hVerSymL⟩ := signProductionHypertreeLayers_sound symMerkleSuite
        multiLeaf4JortsParams sk pk.pkRoot rRand q.grindLimit 1 0 q.epoch mu layerSigs
        Nat.one_pos hEpBound hSymL
      obtain ⟨_, hVerPolyL⟩ := signProductionHypertreeLayers_sound poly257MultiLeafSuite
        multiLeaf4JortsParams sk pk.pkRoot rRand q.grindLimit 1 0 q.epoch mu layerSigs
        Nat.one_pos hEpBound hPolyL
      have hPkSeed : pk.pkSeed = sk.pkSeed := by unfold pk derivePublicKey; rfl
      have hPkRootPoly : computeXmssSubtreeRoot poly257MultiLeafSuite multiLeaf4JortsParams sk 0 0 =
          pk.pkRoot := by unfold pk derivePublicKey; rw [hNumL]; rfl
      have hPkRootSym : computeXmssSubtreeRoot symMerkleSuite multiLeaf4JortsParams sk 0 0 =
          pk.pkRoot := by
        unfold pk; rw [symMerkleSuite_subtreeRoot, derivePublicKey_poly257MultiLeaf, pkFromTbl.public_eqs]
      have hShape : ¬ ((decide (layerSigs.length ≠ multiLeaf4JortsParams.numLayers) ||
          decide ((0 : Nat) ≠ 0)) = true) := by rw [hLenS, hNumL]; decide
      have hVer1 : verifyProductionPqHashSig symMerkleSuite multiLeaf4JortsParams pk q.message
          ⟨rRand, 0, q.epoch, [], layerSigs⟩ = true := by
        rw [verifyProductionPqHashSig_eq]; dsimp only; rw [ite_eq_right hNotOut, ite_eq_right hShape]
        simp only [hStTrue, ↓reduceIte, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true]
        have hMuSym : thPreHash symMerkleSuite pk.pkSeed pk.pkRoot q.message = mu := by
          rw [hPkSeed]; exact hPre q.message
        rw [hMuSym, hPkSeed, hVerSymL]; dsimp only
        rw [show UInt32.ofNat (0 + 1 - 1) = 0 from rfl, hPkRootSym]; exact decide_eq_true rfl
      have hVer2 : verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams pk
          q.message ⟨rRand, 0, q.epoch, [], layerSigs⟩ = true := by
        rw [verifyProductionPqHashSig_eq]; dsimp only; rw [ite_eq_right hNotOut, ite_eq_right hShape]
        simp only [hStTrue, ↓reduceIte, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true]
        rw [hPkSeed, hVerPolyL]; dsimp only
        rw [show UInt32.ofNat (0 + 1 - 1) = 0 from rfl, hPkRootPoly]; exact decide_eq_true rfl
      dsimp only [pk, mu, rRand] at hVer1 hVer2
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
      cases nL with | nil => cases hc.1 | cons b _ => injection hc.1 with hb _
    have hdR : nR.headD 0 = 0xD1 := by
      cases nR with | nil => cases hc.2.2.2.1 | cons b _ => injection hc.2.2.2.1 with hb _
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
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
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
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
    have hDrop2Eq := congrArg (List.drop 2) hEq; rw [hAssocL, hAssocR] at hDrop2Eq
    have hTake12 := congrArg (List.take 12) hDrop2Eq
    rw [List.take_left' hLenL, List.take_left' hP0] at hTake12
    have hDrop12 := congrArg (List.drop 12) hDrop2Eq
    rw [List.drop_left' hLenL, List.drop_left' hP0] at hDrop12
    have hTake12R := congrArg (List.take 12) hDrop12
    rw [List.take_left' hLenR, List.take_left' hP1] at hTake12R
    exact ⟨hdL, hdR, hTake12, hTake12R⟩
  · have hHead := congrArg (fun l => l.headD 0) hEq; rw [rootFromTbl.public_eqs] at hHead; cases hHead

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
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hIdx (by decide))]
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
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
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
  | [] => unfold walkMerkleAuthPathKp at hWalk; cases hWalk
  | [_] =>
    rcases lt4_cases hkp with rfl | rfl | rfl | rfl <;>
      (unfold walkMerkleAuthPathKp at hWalk;
       simp only [(by decide : 0 < 2 ^ 1), (by decide : 1 < 2 ^ 1),
         (by decide : ¬ (2 < 2 ^ 1)), (by decide : ¬ (3 < 2 ^ 1)), ↓reduceIte] at hWalk;
       unfold walkMerkleAuthPathKp at hWalk; cases hWalk)
  | _ :: _ :: _ :: _ =>
    rcases lt4_cases hkp with rfl | rfl | rfl | rfl <;>
      (unfold walkMerkleAuthPathKp at hWalk;
       simp only [(by decide : 0 < 2 ^ 1), (by decide : 1 < 2 ^ 1),
         (by decide : ¬ (2 < 2 ^ 1)), (by decide : ¬ (3 < 2 ^ 1)), ↓reduceIte] at hWalk;
       unfold walkMerkleAuthPathKp at hWalk;
       simp only [(by decide : 0 < 2 ^ 0), (by decide : ¬ (1 < 2 ^ 0)), ↓reduceIte] at hWalk;
       unfold walkMerkleAuthPathKp at hWalk; cases hWalk)
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
      rcases lt4_cases hkp with rfl | rfl | rfl | rfl
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
  rcases lt4_cases hkp with rfl | rfl | rfl | rfl <;>
    rcases lt3_cases hr with rfl | rfl | rfl <;> rfl

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
    if hLo : lo ≤ q.epoch then
      rw [ite_eq_left (Or.inr hLo), ite_eq_left (Or.inr hLo),
        evalLatched_mapTreePost f raw sign (next (sign q)) (q.epoch + 1)]
    else
      have hNot : ¬ ((true = false) ∨ lo ≤ q.epoch) := fun hOr =>
        hOr.elim (fun hb => Bool.noConfusion hb) hLo
      rw [ite_eq_right hNot, ite_eq_right hNot]
      exact evalLatched_mapTreePost f raw sign (next none) lo

def liftSymMerkleAdv {qHash qSign : Nat} (adv : SeedWithheldEufCmaAdv qHash qSign) :
    SeedWithheldEufCmaAdv 0 qSign where
  run pk :=
    mapTreePost (fun ms => (ms.1, canonicalizeSymSigFromPk pk.pkRoot ms.2))
      (evalHashLocallyTree symMerkleSuite.rawHash (adv.run pk))
  bounded pk :=
    mapTreePost_bounded _ _
      (evalHashLocallyTree_bounded symMerkleSuite.rawHash (adv.run pk) (adv.bounded pk))

theorem symMerkleSuite_full_adaptive_forger_bound {nA qHash qSign : Nat}
    (hPos : 0 < (256 * pow256 24) * nA)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜 : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClass : ∀ (s : Fin 12) (c : Fin (pow256 23 * nA)),
      𝒜 (multiLeafInteractivePreAdv (fun a => liftSymMerkleAdv (adv a)) s c))
    {εPre : Spec.RatBound}
    (hPre : Spec.SmDtPreHard 𝒜 multiLeafStep0Th 1 1 1 εPre) :
    Spec.GameBound
      (ExecEufCmaGame hPos symMerkleSuite multiLeaf4JortsParams
        (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) nA).chal z))
        (fun z => adv ((Spec.CoinSplit.prod (256 * pow256 24) nA).advc z))).winProb
      (Spec.RatBound.scale 12 εPre) := by
  have hBase := poly257MultiLeaf_full_adaptive_forger_bound hPos
    (fun a => liftSymMerkleAdv (adv a)) hClass hPre
  refine Spec.GameBound.trans (Spec.event_le_reduction_win _ _ (fun ω hW => ?_)) hBase
  rw [ExecEufCmaGame, execEufCmaGameWith_win] at hW ⊢
  let π₀ := Spec.CoinSplit.prod (256 * pow256 24) nA
  let sk := multiLeaf24Keygen (π₀.chal ω)
  have hPk := symMerkleSuite_derivePublicKey sk
  have hLogEq : ∀ qs, productionSigningLog symMerkleSuite multiLeaf4JortsParams sk qs =
      productionSigningLog poly257MultiLeafSuite multiLeaf4JortsParams sk qs := by
    intro qs; induction qs with
    | nil => rw [productionSigningLog_nil, productionSigningLog_nil]
    | cons q rest ih =>
      rw [productionSigningLog_cons, productionSigningLog_cons, symMerkleSuite_prodSignQuery_eq, ih]
  unfold execEufCmaOutcome at hW ⊢; unfold liftSymMerkleAdv; dsimp only at hW ⊢
  rw [symMerkleSuite_derivePublicKey] at hW
  rw [evalLatched_mapTreePost,
    ← evalLatched_evalHashLocallyTree symMerkleSuite.rawHash poly257MultiLeafSuite.rawHash
        (prodSignQuery symMerkleSuite multiLeaf4JortsParams sk)
        (prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams sk)
        (symMerkleSuite_prodSignQuery_eq sk)]
  dsimp only [π₀, sk] at hLogEq
  rw [prodEufCmaWin_eq, symMerkleSuite_derivePublicKey, hLogEq] at hW
  obtain ⟨hVerSym, hFresh⟩ := Bool.and_eq_true_iff.mp hW
  rw [prodEufCmaWin_eq]; dsimp only; refine Bool.and_eq_true_iff.mpr ⟨?_, hFresh⟩
  let msgStar := (evalLatchedAdaptiveTree true symMerkleSuite.rawHash
    (prodSignQuery symMerkleSuite multiLeaf4JortsParams sk)
    ((adv (π₀.advc ω)).run (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk)) 0).1.1
  let sigStar := (evalLatchedAdaptiveTree true symMerkleSuite.rawHash
    (prodSignQuery symMerkleSuite multiLeaf4JortsParams sk)
    ((adv (π₀.advc ω)).run (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk)) 0).1.2
  change verifyProductionPqHashSig symMerkleSuite multiLeaf4JortsParams
    (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk) msgStar sigStar = true at hVerSym
  obtain ⟨_, hLen1, hLt4, hHt⟩ := verifyProductionPqHashSig_stateful_inv symMerkleSuite
    multiLeaf4JortsParams _ msgStar sigStar (by rw [multiLeaf4JortsParams.public_eqs]) hVerSym
  have hLsigSingleton : ∃ lsig, sigStar.layerSigs = [lsig] := by
    cases hLs : sigStar.layerSigs with
    | nil => rw [hLs, multiLeaf4JortsParams.public_eqs] at hLen1; cases hLen1
    | cons l rest =>
      cases rest with
      | nil => exact ⟨l, rfl⟩
      | cons _ _ =>
        rw [hLs, multiLeaf4JortsParams.public_eqs] at hLen1
        dsimp only [List.length] at hLen1
        exact absurd (Nat.succ.inj hLen1) (Nat.succ_ne_zero _)
  obtain ⟨lsig, hLsEq⟩ := hLsigSingleton
  have hPkRootEq : (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot =
      rootFromTbl (honestSlotHiLo sk) := by rw [derivePublicKey_poly257MultiLeaf, pkFromTbl.public_eqs]
  have hPkSeedEq : (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkSeed =
      sk.pkSeed := by rw [derivePublicKey_poly257MultiLeaf, pkFromTbl.public_eqs]
  have hAuthTblEq : authPathFromTbl
      (fun kp r => let base := 2 + 6 * kp + 2 * r
        ((rootFromTbl (honestSlotHiLo sk)).getD base 0, (rootFromTbl (honestSlotHiLo sk)).getD (base + 1) 0))
      sigStar.leafGlobalIdx = authPathFromTbl (honestSlotHiLo sk) sigStar.leafGlobalIdx := by
    have hLeaf : ∀ j < 4, leafFromTbl (fun kp r => let base := 2 + 6 * kp + 2 * r
        ((rootFromTbl (honestSlotHiLo sk)).getD base 0, (rootFromTbl (honestSlotHiLo sk)).getD (base + 1) 0)) j =
        leafFromTbl (honestSlotHiLo sk) j := fun j hj => by
      rw [leafFromTbl.public_eqs, leafFromTbl.public_eqs, tblFromPkRoot_eq_honest sk hj (by decide),
        tblFromPkRoot_eq_honest sk hj (by decide), tblFromPkRoot_eq_honest sk hj (by decide)]
    have hNode : ∀ idx < 2, node1FromTbl (fun kp r => let base := 2 + 6 * kp + 2 * r
        ((rootFromTbl (honestSlotHiLo sk)).getD base 0, (rootFromTbl (honestSlotHiLo sk)).getD (base + 1) 0)) idx =
        node1FromTbl (honestSlotHiLo sk) idx := fun idx hIdx => by
      have hC : idx = 0 ∨ idx = 1 := match idx with
        | 0 => .inl rfl | 1 => .inr rfl | _ + 2 => False.elim (Nat.not_lt_zero _ (Nat.lt_of_add_lt_add_right hIdx))
      rcases hC with rfl | rfl <;> (rw [node1FromTbl.public_eqs, node1FromTbl.public_eqs,
        tblFromPkRoot_eq_honest sk (by decide) (by decide), tblFromPkRoot_eq_honest sk (by decide) (by decide),
        tblFromPkRoot_eq_honest sk (by decide) (by decide), tblFromPkRoot_eq_honest sk (by decide) (by decide),
        tblFromPkRoot_eq_honest sk (by decide) (by decide), tblFromPkRoot_eq_honest sk (by decide) (by decide)])
    rw [authPathFromTbl.public_eqs, authPathFromTbl.public_eqs]; repeat' split
    all_goals simp only [hLeaf 0 (by decide), hLeaf 1 (by decide), hLeaf 2 (by decide),
      hLeaf 3 (by decide), hNode 0 (by decide), hNode 1 (by decide)]
  change verifyProductionPqHashSig poly257MultiLeafSuite multiLeaf4JortsParams
    (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk) msgStar
    (canonicalizeSymSigFromPk (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams sk).pkRoot sigStar) = true
  unfold canonicalizeSymSigFromPk; rw [hLsEq, hPkRootEq]; dsimp only; rw [hAuthTblEq]
  rw [verifyProductionPqHashSig_eq] at hVerSym ⊢; dsimp only
  split at hVerSym
  · cases hVerSym
  · rename_i hRangeOk; rw [ite_eq_right hRangeOk]; split at hVerSym
    · cases hVerSym
    · rename_i hShapeOk
      have hShapeOk' : ¬ ([LayerXmssSig.mk lsig.tswCtr lsig.wotsChains
          (authPathFromTbl (honestSlotHiLo sk) sigStar.leafGlobalIdx)].length ≠
          multiLeaf4JortsParams.numLayers || sigStar.msgTswCtr ≠ 0) := by rw [hLsEq] at hShapeOk; exact hShapeOk
      rw [ite_eq_right hShapeOk']
      have hStT : multiLeaf4JortsParams.statefulJorts = true := by rw [multiLeaf4JortsParams.public_eqs]
      simp only [hStT, ↓reduceIte] at hVerSym ⊢; split at hVerSym
      · cases hVerSym
      · rename_i hEmptyOk; rw [ite_eq_right hEmptyOk]
        rw [hLsEq, hPkSeedEq, hPkRootEq] at hHt; rw [hPkSeedEq, hPkRootEq]
        have hPreEq : thPreHash symMerkleSuite sk.pkSeed (rootFromTbl (honestSlotHiLo sk)) msgStar =
            thPreHash poly257MultiLeafSuite sk.pkSeed (rootFromTbl (honestSlotHiLo sk)) msgStar := by
          rw [thPreHash_eq, thPreHash_eq]; exact symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.1
        rw [hPreEq, verifyProductionHypertreeLayers_cons] at hHt
        rw [verifyProductionHypertreeLayers_cons]; dsimp only at hHt ⊢
        rw [show UInt32.ofNat 0 = (0 : UInt32) from rfl] at hHt ⊢
        split at hHt
        · cases hHt
        · rename_i hCtrOk; rw [ite_eq_right hCtrOk]
          have hDigEq : productionLayerDigest symMerkleSuite multiLeaf4JortsParams sigStar.rRand
              sk.pkSeed (rootFromTbl (honestSlotHiLo sk))
              (thPreHash poly257MultiLeafSuite sk.pkSeed (rootFromTbl (honestSlotHiLo sk)) msgStar)
              0 (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ multiLeaf4JortsParams.subtreeHeight))
              (UInt32.ofNat (sigStar.leafGlobalIdx % 2 ^ multiLeaf4JortsParams.subtreeHeight)) lsig.tswCtr =
              productionLayerDigest poly257MultiLeafSuite multiLeaf4JortsParams sigStar.rRand
                sk.pkSeed (rootFromTbl (honestSlotHiLo sk))
                (thPreHash poly257MultiLeafSuite sk.pkSeed (rootFromTbl (honestSlotHiLo sk)) msgStar)
                0 (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ multiLeaf4JortsParams.subtreeHeight))
                (UInt32.ofNat (sigStar.leafGlobalIdx % 2 ^ multiLeaf4JortsParams.subtreeHeight)) lsig.tswCtr := by
            rw [productionLayerDigest_eq, productionLayerDigest_eq]
            simp only [hStT, decide_true, Bool.true_and, ↓reduceIte, thHashLeafMsg_eq]
            exact symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.1
          rw [hDigEq] at hHt
          cases hExt : extractBaseWDigitsChecked multiLeaf4JortsParams.w multiLeaf4JortsParams.ell1
              (productionLayerDigest poly257MultiLeafSuite multiLeaf4JortsParams sigStar.rRand
                sk.pkSeed (rootFromTbl (honestSlotHiLo sk))
                (thPreHash poly257MultiLeafSuite sk.pkSeed (rootFromTbl (honestSlotHiLo sk)) msgStar)
                0 (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ multiLeaf4JortsParams.subtreeHeight))
                (UInt32.ofNat (sigStar.leafGlobalIdx % 2 ^ multiLeaf4JortsParams.subtreeHeight)) lsig.tswCtr) with
          | none => rw [hExt] at hHt; cases hHt
          | some digits =>
            rw [hExt] at hHt; dsimp only at hHt ⊢; split at hHt
            · cases hHt
            · rename_i hTswOk; rw [ite_eq_right hTswOk]; split at hHt
              · cases hHt
              · rename_i hChainsLenOk; rw [ite_eq_right hChainsLenOk]
                have hKpMod : sigStar.leafGlobalIdx % 2 ^ multiLeaf4JortsParams.subtreeHeight =
                    sigStar.leafGlobalIdx := by
                  rw [multiLeaf4JortsParams.public_eqs] at hLt4 ⊢; exact Nat.mod_eq_of_lt hLt4
                have hTreeDiv : sigStar.leafGlobalIdx / 2 ^ multiLeaf4JortsParams.subtreeHeight = 0 := by
                  rw [multiLeaf4JortsParams.public_eqs] at hLt4 ⊢; exact Nat.div_eq_of_lt hLt4
                have hRecEq : recoverWotsPkFromSig symMerkleSuite multiLeaf4JortsParams sk.pkSeed
                    0 0 sigStar.leafGlobalIdx digits lsig.wotsChains =
                    recoverWotsPkFromSig poly257MultiLeafSuite multiLeaf4JortsParams sk.pkSeed
                      0 0 sigStar.leafGlobalIdx digits lsig.wotsChains := by
                  rw [recoverWotsPkFromSig_eq, recoverWotsPkFromSig_eq, thTweakTl_eq, thTweakTl_eq,
                    symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.2.2,
                    recoverWotsEndpoints_eq, recoverWotsEndpoints_eq]
                  congr 1; apply List.map_congr_left; intro r _
                  have hSt : ∀ (k s : Nat) (x : List UInt8),
                      wotsChainSteps symMerkleSuite sk.pkSeed 0 0 sigStar.leafGlobalIdx r s k x =
                        wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 sigStar.leafGlobalIdx r s k x := by
                    intro k; induction k with
                    | zero => intro s x; rw [wotsChainSteps_zero, wotsChainSteps_zero]
                    | succ k' ih =>
                      intro s x; rw [wotsChainSteps_succ, wotsChainSteps_succ]; dsimp only
                      rw [thChainF_eq, thChainF_eq, symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.2.1]
                      exact ih (s + 1) _
                  exact hSt _ _ _
                simp only [hKpMod, hTreeDiv, show UInt64.ofNat 0 = (0 : UInt64) from rfl] at hHt ⊢
                rw [hRecEq] at hHt
                let wPk := recoverWotsPkFromSig poly257MultiLeafSuite multiLeaf4JortsParams
                  sk.pkSeed 0 0 sigStar.leafGlobalIdx digits lsig.wotsChains
                have hKpLt4 : sigStar.leafGlobalIdx < 4 := by
                  rw [multiLeaf4JortsParams.public_eqs] at hLt4; exact hLt4
                cases hW : walkMerkleAuthPathKp symMerkleSuite sk.pkSeed 0 0 .tree 0
                    multiLeaf4JortsParams.subtreeHeight 0 sigStar.leafGlobalIdx wPk lsig.authPath with
                | none =>
                  dsimp only [wPk] at hW; rw [hW] at hHt; cases hHt
                | some topR =>
                  have hW' := hW; dsimp only [wPk] at hW'
                  rw [hW'] at hHt; dsimp only at hHt
                  rw [verifyProductionHypertreeLayers_nil] at hHt; injection hHt with hTopEq; subst hTopEq
                  have hSubH2 : multiLeaf4JortsParams.subtreeHeight = 2 := by rw [multiLeaf4JortsParams.public_eqs]
                  rw [hSubH2] at hW ⊢
                  have hWpkEq : wPk = leafFromTbl (honestSlotHiLo sk) sigStar.leafGlobalIdx := by
                    dsimp only [wPk] at hW ⊢; rw [recoverWotsPkFromSig_eq] at hW ⊢
                    exact symMerkleSuite_walk_pins_wotsPk sk.pkSeed sk hKpLt4 hW
                  dsimp only [wPk] at hWpkEq
                  rw [hWpkEq, poly257MultiLeaf_walkAuthPath_honest sk hKpLt4]; dsimp only
                  rw [hPkRootEq, verifyProductionHypertreeLayers_nil]; exact decide_eq_true rfl

/-- **Zeroed-Address Cross-Epoch Forger (`zeroedAdrsEpochForger`).** -/
def zeroedAdrsEpochForger : SeedWithheldEufCmaAdv 3 2 where
  run pk :=
    .signQuery ⟨[0, 0], [], 0, 1⟩ (fun sig0Opt =>
      .signQuery ⟨[0, 1], [], 1, 1⟩ (fun sig1Opt =>
        let lsig0 := match sig0Opt with | some s => s.layerSigs.headD ⟨0, [], []⟩ | none => ⟨0, [], []⟩
        let lsig1 := match sig1Opt with | some s => s.layerSigs.headD ⟨0, [], []⟩ | none => ⟨0, [], []⟩
        stepChain3Adaptive pk.pkSeed 0 2 (lsig0.wotsChains.getD 2 zero32) (fun c2End =>
          .pure ([0, 2], ⟨zero32, 0, 0, [],
            [⟨0, lsig0.wotsChains.getD 0 zero32 :: lsig1.wotsChains.getD 1 zero32 :: c2End ::
              List.replicate 125 crumb32, lsig0.authPath⟩]⟩))))
  bounded pk := by
    intro s0 s1; dsimp only; rw [stepChain3Adaptive.public_eqs]; exact fun _ _ _ => trivial

/-- **`#tooth` Zeroing `HashAdrs` `layer`/`keyPair` (`zeroKpLayerOfSuite`) Breaks EUF-CMA With
    Probability `1` Even With `BeltLatch` ON and `checkTargetSum` ON.** -/
theorem tooth_zeroed_adrs_leaf_layer_forges_prob_one :
    let hPos : 0 < (256 * pow256 24) * 1 :=
      Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos
    let keygen := fun z : Fin ((256 * pow256 24) * 1) =>
      multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z)
    let adv := fun _ : Fin ((256 * pow256 24) * 1) => zeroedAdrsEpochForger
    (∀ ω : Fin ((256 * pow256 24) * 1),
      (ExecEufCmaGame hPos (zeroKpLayerOfSuite symMerkleSuite) multiLeaf4JortsParams
        keygen adv).win ω = true) ∧
    ¬ Spec.GameBound
        (ExecEufCmaGame hPos (zeroKpLayerOfSuite symMerkleSuite) multiLeaf4JortsParams
          keygen adv).winProb
        (Spec.RatBound.scale 12 ⟨2, 256, by decide⟩) := by
  intro hPos keygen adv
  let zSuite := zeroKpLayerOfSuite symMerkleSuite
  have hZeroChain : ∀ (sk : PqSecretKey) (kp r k : Nat),
      wotsChainSteps zSuite sk.pkSeed 0 0 kp r 0 k (wotsSecretBase zSuite sk 0 0 kp r) =
      wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r 0 k
        (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r) := fun sk kp r k => by
    have hSec : wotsSecretBase zSuite sk 0 0 kp r = wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r := by
      rw [wotsSecretBase_eq, wotsSecretBase_eq, thSecretPrf_eq, thSecretPrf_eq,
        zeroKpLayerOfSuite_thCall, symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.1]; rfl
    have hSt : ∀ (n s : Nat) (x : List UInt8),
        wotsChainSteps zSuite sk.pkSeed 0 0 kp r s n x =
          wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r s n x := fun n => by
      induction n with
      | zero => intro s x; rw [wotsChainSteps_zero, wotsChainSteps_zero]
      | succ n' ih =>
        intro s x; rw [wotsChainSteps_succ, wotsChainSteps_succ]; dsimp only
        rw [thChainF_eq, thChainF_eq, zeroKpLayerOfSuite_thCall,
          symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.2.1]; exact ih (s + 1) _
    rw [hSec, hSt]
  have hZeroWotsPk : ∀ sk kp,
      computeWotsPk zSuite multiLeaf4JortsParams sk 0 0 kp = leafFromTbl (honestSlotHiLo sk) 0 := fun sk kp => by
    rw [← poly257MultiLeaf_computeWotsPk_eq sk (by decide : 0 < 4),
      computeWotsPk_eq, computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq,
      zeroKpLayerOfSuite_thCall, symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.2.2]
    congr 1; apply List.map_congr_left; intro r _; exact hZeroChain sk kp r _
  let constTbl (sk : PqSecretKey) : Nat → Nat → UInt8 × UInt8 := fun _ r => honestSlotHiLo sk 0 r
  have hZeroRoot : ∀ sk, computeXmssSubtreeRoot zSuite multiLeaf4JortsParams sk 0 0 =
      rootFromTbl (constTbl sk) := by
    intro sk; rw [computeXmssSubtreeRoot_eq]
    have hSubH : multiLeaf4JortsParams.subtreeHeight = 2 := by rw [multiLeaf4JortsParams.public_eqs]
    have hc1 : UInt32.ofNat (0 + 1) = 1 := rfl
    have hc2 : UInt32.ofNat (1 + 1) = 2 := rfl
    have hu0 : UInt32.ofNat 0 = 0 := rfl
    rw [hSubH, computeMerkleNode_succ, computeMerkleNode_succ, computeMerkleNode_succ,
      computeMerkleNode_zero, computeMerkleNode_zero, computeMerkleNode_zero,
      computeMerkleNode_zero]; dsimp only
    rw [hc1, hc2, hu0, hZeroWotsPk, hZeroWotsPk, hZeroWotsPk, hZeroWotsPk]
    have hL0 := leafFromTbl_shape (honestSlotHiLo sk) 0
    have hTh1 : ∀ idx < 2, thNodeH zSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat idx⟩
          (leafFromTbl (honestSlotHiLo sk) 0) (leafFromTbl (honestSlotHiLo sk) 0) =
        node1FromTbl (constTbl sk) idx := fun idx hIdx => by
      rw [thNodeH_eq, zeroKpLayerOfSuite_thCall]; dsimp only
      rw [← thNodeH_eq,
        symMerkleSuite_thNodeH_h1 sk.pkSeed 0 idx _ _ hIdx ⟨hL0.1, hL0.2.1, hL0.2.2.1⟩
          ⟨hL0.1, hL0.2.1, hL0.2.2.1⟩, hL0.2.2.2, node1FromTbl.public_eqs]
    have hTh0 : thNodeH zSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, 0⟩
        (leafFromTbl (honestSlotHiLo sk) 0) (leafFromTbl (honestSlotHiLo sk) 0) =
        node1FromTbl (constTbl sk) 0 := by
      change thNodeH zSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat 0⟩ _ _ = _
      exact hTh1 0 (by decide)
    have hTh1' : thNodeH zSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, 1⟩
        (leafFromTbl (honestSlotHiLo sk) 0) (leafFromTbl (honestSlotHiLo sk) 0) =
        node1FromTbl (constTbl sk) 1 := by
      change thNodeH zSuite sk.pkSeed ⟨0, 0, .tree, 0, 1, UInt32.ofNat 1⟩ _ _ = _
      exact hTh1 1 (by decide)
    rw [hTh0, hTh1']
    have hM0 := node1FromTbl_shape (constTbl sk) 0
    have hM1 := node1FromTbl_shape (constTbl sk) 1
    rw [thNodeH_eq, zeroKpLayerOfSuite_thCall]; dsimp only
    rw [← thNodeH_eq, symMerkleSuite_thNodeH_h2 sk.pkSeed 0 _ _
      ⟨hM0.1, hM0.2.1, hM0.2.2.1⟩ ⟨hM1.1, hM1.2.1, hM1.2.2.1⟩,
      hM0.2.2.2, hM1.2.2.2, rootFromTbl.public_eqs]
    simp only [List.append_assoc]
  have hZeroPk : ∀ sk, derivePublicKey zSuite multiLeaf4JortsParams sk =
      pkFromTbl sk.pkSeed (constTbl sk) := fun sk => by
    rw [pkFromTbl.public_eqs]; unfold derivePublicKey
    have hTop : UInt32.ofNat (multiLeaf4JortsParams.numLayers - 1) = 0 := by
      rw [multiLeaf4JortsParams.public_eqs]; rfl
    rw [hTop]; dsimp only; rw [hZeroRoot]
  have hZeroSign : ∀ (sk : PqSecretKey) (ep sub : Nat), ep < 4 → sub < 3 →
      prodSignQuery zSuite multiLeaf4JortsParams sk ⟨[0, UInt8.ofNat sub], [], ep, 1⟩ =
      some ⟨zero32, 0, ep, [], [⟨0,
        (List.range 128).map (fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r)),
        buildMerkleAuthPathKp zSuite sk.pkSeed 0 0 .tree 0
          (computeWotsPk zSuite multiLeaf4JortsParams sk 0 0) 2 0 0 ep⟩]⟩ := by
    intro sk ep sub hep hsub
    have hStT : multiLeaf4JortsParams.statefulJorts = true := by rw [multiLeaf4JortsParams.public_eqs]
    rw [prodSignQuery_eq, ite_eq_left hStT, evalProductionStatefulSign_eq]
    have hNotOut0 : ¬ ((!multiLeaf4JortsParams.statefulJorts ||
        !multiLeaf4JortsParams.productionWellFormed ||
        !multiLeaf4JortsParams.productionLeafIdxInRange ep) = true) := by
      rw [hStT, multiLeaf4JortsParams_productionWellFormed, multiLeaf4Jorts_leafIdxInRange,
        decide_eq_true hep]; decide
    rw [ite_eq_right hNotOut0]; dsimp only
    have hPkS0 : (derivePublicKey zSuite multiLeaf4JortsParams sk).pkSeed = sk.pkSeed := by
      unfold derivePublicKey; rfl
    rw [hPkS0]
    have hMod : ep % 4 = ep := Nat.mod_eq_of_lt hep
    have hZa : ({ zeroAdrs with layer := 0, keyPair := 0 } : HashAdrs) = zeroAdrs := by
      rw [zeroAdrs.public_eqs]
    have hMu : thPreHash zSuite sk.pkSeed (derivePublicKey zSuite multiLeaf4JortsParams sk).pkRoot
        [0, UInt8.ofNat sub] = [0xE0, 0, UInt8.ofNat sub] ++ List.replicate 29 0x00 := by
      rw [thPreHash_eq, zeroKpLayerOfSuite_thCall,
        symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.1, hZa,
        ← thPreHash_eq, poly257MultiLeaf_thPreHash_eq]
      have hSub8 : (UInt8.ofNat sub).toNat = sub := by
        rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hsub (by decide))]
      dsimp only; rw [hSub8]; exact ite_eq_left ⟨by decide, hsub⟩
    have hPrf : ∀ mu, thPrfMsg zSuite sk.skPrf [] mu = zero32 := fun mu => by
      rw [thPrfMsg_eq, zeroKpLayerOfSuite_thCall,
        symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.1, hZa,
        ← thPrfMsg_eq, poly257MultiLeaf_thPrfMsg_eq]
    rw [hMu, hPrf, signProductionHypertreeCore_def]
    have hNumL : multiLeaf4JortsParams.numLayers = 1 := by rw [multiLeaf4JortsParams.public_eqs]
    simp only [hStT, hNumL, ↓reduceIte]
    have hSignZ : signProductionHypertreeLayers zSuite multiLeaf4JortsParams sk
        (derivePublicKey zSuite multiLeaf4JortsParams sk).pkRoot zero32 1 0 ep
        ([0xE0, 0, UInt8.ofNat sub] ++ List.replicate 29 0x00) 1 =
      some [⟨0,
        (List.range 128).map (fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r)),
        buildMerkleAuthPathKp zSuite sk.pkSeed 0 0 .tree 0
          (computeWotsPk zSuite multiLeaf4JortsParams sk 0 0) 2 0 0 ep⟩] := by
      have hDiv : ep / 4 = 0 := Nat.div_eq_of_lt hep
      rw [signProductionHypertreeLayers_succ]; simp only [multiLeaf4JortsParams.public_eqs]
      rw [hMod, hDiv]
      simp only [decide_true, Bool.and_self, ↓reduceIte, PqHashParams.targetSum_eq,
        show (128 * (4 - 1)) / 2 = 192 from rfl,
        show UInt64.ofNat 0 = (0 : UInt64) from rfl,
        show UInt32.ofNat 0 = (0 : UInt32) from rfl]
      rw [grindTswLeafCounterAux_succ]
      simp only [(by decide : 0 < 2 ^ 32), decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [← multiLeaf4JortsParams.public_eqs]
      have hHm : thHashLeafMsg zSuite zero32 sk.pkSeed
          (derivePublicKey zSuite multiLeaf4JortsParams sk).pkRoot
          ([0xE0, 0, UInt8.ofNat sub] ++ List.replicate 29 0x00) 0 (UInt32.ofNat ep) 0 =
          encodeSubMsg3Hmsg sub := by
        rw [thHashLeafMsg_eq, zeroKpLayerOfSuite_thCall,
          symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.1]; dsimp only
        change thCall poly257MultiLeafSuite tagHMsg sk.pkSeed ⟨0, 0, .wotsHash, 0, 0, UInt32.ofNat 0⟩ _ = _
        rw [← thHashLeafMsg_eq, poly257MultiLeaf_thHashLeafMsg_eq]
        have hSub8 : (UInt8.ofNat sub).toNat = sub := by
          rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hsub (by decide))]
        simp only [List.cons_append, List.nil_append]
        rw [hSub8]; exact ite_eq_left ⟨by decide, hsub, rfl, trivial⟩
      rw [hHm]
      obtain ⟨hExtSub, hChkSub⟩ :
          extractBaseWDigitsChecked 4 128 (encodeSubMsg3Hmsg sub) =
            some (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)) ∧
          checkTargetSum 4 128 192 (extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)) = true := by
        rcases lt3_cases hsub with rfl | rfl | rfl <;>
          (simp only [encodeSubMsg3Hmsg.public_eqs, extractBaseWDigitsChecked_eq,
             extractBaseWDigits_eq, checkTargetSum, sumDigits_eq_foldr];
           exact ⟨by decide +kernel, by decide +kernel⟩)
      rw [hExtSub]; dsimp only; rw [hChkSub, ite_eq_left rfl, signProductionHypertreeLayers_zero]; dsimp only
      have hChZ : ((List.range 128).map fun r => wotsChainSteps zSuite sk.pkSeed 0 0 ep r 0
            ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD r 0) (wotsSecretBase zSuite sk 0 0 ep r)) =
          ((List.range 128).map fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r 0
            ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg sub)).getD r 0)
            (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r)) :=
        List.map_congr_left (fun r _ => hZeroChain sk ep r _)
      rw [hChZ]
    have hEpB : ep < 2 ^ (1 * multiLeaf4JortsParams.subtreeHeight) := by
      rw [multiLeaf4JortsParams.public_eqs]; exact hep
    obtain ⟨_, hVerZL⟩ := signProductionHypertreeLayers_sound zSuite multiLeaf4JortsParams sk
      (derivePublicKey zSuite multiLeaf4JortsParams sk).pkRoot zero32 1 1 0 ep
      ([0xE0, 0, UInt8.ofNat sub] ++ List.replicate 29 0x00) _ Nat.one_pos hEpB hSignZ
    rw [hSignZ]; dsimp only
    refine ite_eq_left ?_
    rw [verifyProductionPqHashSig_eq]
    have hWf := multiLeaf4JortsParams_productionWellFormed
    have hRng : multiLeaf4JortsParams.productionLeafIdxInRange ep = true := by
      rw [multiLeaf4Jorts_leafIdxInRange]; exact decide_eq_true hep
    have hSh : (decide ((1 : Nat) ≠ multiLeaf4JortsParams.numLayers) || decide ((0 : Nat) ≠ 0)) = false := by
      rw [multiLeaf4JortsParams.public_eqs]; rfl
    have hPkS : (derivePublicKey zSuite multiLeaf4JortsParams sk).pkSeed = sk.pkSeed := by
      unfold derivePublicKey; rfl
    have hPkR : computeXmssSubtreeRoot zSuite multiLeaf4JortsParams sk 0 0 =
        (derivePublicKey zSuite multiLeaf4JortsParams sk).pkRoot := by
      unfold derivePublicKey; rw [hNumL]; rfl
    simp only [hWf, hRng, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, List.length_nil, hSh, hStT, List.isEmpty_nil]
    rw [hPkS, hMu, hVerZL]; dsimp only
    rw [show UInt32.ofNat (0 + 1 - 1) = 0 from rfl, hPkR]; exact decide_eq_true rfl
  have hForallWin : ∀ ω : Fin ((256 * pow256 24) * 1),
      (ExecEufCmaGame hPos zSuite multiLeaf4JortsParams keygen adv).win ω = true := by
    intro ω
    let sk := keygen ω
    have hS0 := hZeroSign sk 0 0 (by decide) (by decide)
    have hS1 := hZeroSign sk 1 1 (by decide) (by decide)
    have hS2 := hZeroSign sk 0 2 (by decide) (by decide)
    rw [show UInt8.ofNat 0 = (0 : UInt8) from rfl] at hS0
    rw [show UInt8.ofNat 1 = (1 : UInt8) from rfl] at hS1
    rw [show UInt8.ofNat 2 = (2 : UInt8) from rfl] at hS2
    have hStepZ : ∀ (st : UInt32) (cur : List UInt8),
        zSuite.rawHash (thPreimage tagThF sk.pkSeed ⟨0, 0, .wotsHash, 0, 2, st⟩ [cur]) =
        thChainF poly257MultiLeafSuite sk.pkSeed ⟨0, 0, .wotsHash, 0, 2, st⟩ cur := fun st cur => by
      rw [← thCall_eq, zeroKpLayerOfSuite_thCall,
        symMerkleSuite_nonThH_eq _ _ _ _ symMerkleSuite_role_ne.2.2.2.2.1, thChainF_eq]
    have hEvalStep3 : ∀ (x : List UInt8) (k : List UInt8 → ProdAdaptiveTree (List UInt8 × PqHashSig))
        (lo : Nat),
        evalLatchedAdaptiveTree true zSuite.rawHash (prodSignQuery zSuite multiLeaf4JortsParams sk)
          (stepChain3Adaptive sk.pkSeed 0 2 x k) lo =
        evalLatchedAdaptiveTree true zSuite.rawHash (prodSignQuery zSuite multiLeaf4JortsParams sk)
          (k (wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 2 0 3 x)) lo := fun x k lo => by
      rw [stepChain3Adaptive.public_eqs]; simp only [evalLatchedAdaptiveTree.public_eqs]
      rw [show UInt32.ofNat 0 = (0 : UInt32) from rfl, show UInt32.ofNat 2 = (2 : UInt32) from rfl,
        hStepZ, hStepZ, hStepZ,
        wotsChainSteps_succ, wotsChainSteps_succ, wotsChainSteps_succ, wotsChainSteps_zero]; rfl
    have hPkSeed : (derivePublicKey zSuite multiLeaf4JortsParams sk).pkSeed = sk.pkSeed := by
      rw [hZeroPk, pkFromTbl.public_eqs]
    rw [ExecEufCmaGame, execEufCmaGameWith_win]
    have hGet0 : ((List.range 128).map (fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r))).getD 0 zero32 =
        wotsSecretBase poly257MultiLeafSuite sk 0 0 0 0 := by
      rw [list_getD_map_range 128 _ zero32 (by decide), encodeSubMsg3Hmsg_explicit_digits.1, wotsChainSteps_zero]
    have hGet1 : ((List.range 128).map (fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 1)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r))).getD 1 zero32 =
        wotsSecretBase poly257MultiLeafSuite sk 0 0 0 1 := by
      rw [list_getD_map_range 128 _ zero32 (by decide), encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.1, wotsChainSteps_zero]
    have hGet2 : ((List.range 128).map (fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r))).getD 2 zero32 =
        wotsSecretBase poly257MultiLeafSuite sk 0 0 0 2 := by
      rw [list_getD_map_range 128 _ zero32 (by decide), encodeSubMsg3Hmsg_explicit_digits.2.2.1, wotsChainSteps_zero]
    have hOut : execEufCmaOutcome true zSuite multiLeaf4JortsParams keygen adv ω =
        ⟨sk, [⟨[0, 0], [], 0, 1⟩, ⟨[0, 1], [], 1, 1⟩], [0, 2],
         ⟨zero32, 0, 0, [], [⟨0,
           wotsSecretBase poly257MultiLeafSuite sk 0 0 0 0 ::
           wotsSecretBase poly257MultiLeafSuite sk 0 0 0 1 ::
           wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 2 0 3
             (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 2) :: List.replicate 125 crumb32,
           buildMerkleAuthPathKp zSuite sk.pkSeed 0 0 .tree 0
             (computeWotsPk zSuite multiLeaf4JortsParams sk 0 0) 2 0 0 0⟩]⟩⟩ := by
      unfold execEufCmaOutcome; dsimp only [adv, zeroedAdrsEpochForger]
      rw [show keygen ω = sk from rfl,
        evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0)), hS0,
        evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.le_refl 1)), hS1]
      dsimp only [List.headD]
      rw [hPkSeed, hGet0, hGet1, hGet2, hEvalStep3]
      simp only [evalLatchedAdaptiveTree.public_eqs]
    rw [hOut, prodEufCmaWin_eq]; dsimp only
    rw [productionSigningLog_cons, hS0, productionSigningLog_cons, hS1, productionSigningLog_nil]
    dsimp only [List.append, List.map]
    refine Bool.and_eq_true_iff.mpr
      ⟨?_, decide_eq_true (by decide : ([0, 2] : List UInt8) ∉ [[0, 0], [0, 1]])⟩
    have hS2Ver := prodSignQuery_verifies zSuite multiLeaf4JortsParams sk ⟨[0, 2], [], 0, 1⟩ _ hS2
    have hChainsEq :
        wotsSecretBase poly257MultiLeafSuite sk 0 0 0 0 ::
        wotsSecretBase poly257MultiLeafSuite sk 0 0 0 1 ::
        wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 2 0 3
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 2) :: List.replicate 125 crumb32 =
        (List.range 128).map (fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r 0
          ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 2)).getD r 0)
          (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r)) := by
      have hSplit : List.range 128 = 0 :: 1 :: 2 :: (List.range 125).map (· + 3) := by decide
      rw [hSplit, List.map_cons, List.map_cons, List.map_cons, List.map_map,
        encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.2.2.1, wotsChainSteps_zero,
        encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.2.2.2.1, wotsChainSteps_zero,
        encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.2.2.2.2]; congr 3
      have hEach : ∀ k ∈ List.range 125,
          ((fun r => wotsChainSteps poly257MultiLeafSuite sk.pkSeed 0 0 0 r 0
            ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 2)).getD r 0)
            (wotsSecretBase poly257MultiLeafSuite sk 0 0 0 r)) ∘ (· + 3)) k = crumb32 := by
        intro k hk; have hkLt : k < 125 := List.mem_range.mp hk
        dsimp only [Function.comp_def]; rw [wotsSecretBase_eq, poly257MultiLeaf_thSecretPrf]; dsimp only
        have hu0 : (UInt32.ofNat 0).toNat = 0 := rfl
        have hr32 : (UInt32.ofNat (k + 3)).toNat = k + 3 := by
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans (Nat.add_lt_add_right hkLt 3) (by decide))]
        rw [hu0, hr32, ite_eq_right (fun h => Nat.not_lt_zero k (Nat.lt_of_add_lt_add_right h.2))]
        exact poly257MultiLeaf_inactive_crumb sk.pkSeed (by decide) (Nat.le_add_left 3 k)
          (Nat.add_lt_add_right hkLt 3) _ 0
      exact ((List.map_congr_left hEach).trans
        (List.map_const'.trans (by rw [List.length_range]))).symm
    rw [hChainsEq]; exact hS2Ver
  exact ⟨hForallWin, Spec.FinGame.not_bound_of_forall_win _ hForallWin (by decide)⟩

theorem tooth_zeroed_adrs_refutes_bound :
    ¬ Spec.GameBound
        (ExecEufCmaGame (Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos)
          (zeroKpLayerOfSuite symMerkleSuite) multiLeaf4JortsParams
          (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z))
          (fun _ => zeroedAdrsEpochForger)).winProb
        (Spec.RatBound.scale 12 ⟨2, 256, by decide⟩) :=
  tooth_zeroed_adrs_leaf_layer_forges_prob_one.2

#verify_constructive
  Qsag.zeroKpLayerOfSuite_thCall
  Qsag.symMerkleSuite_full_adaptive_forger_bound
  Qsag.tooth_zeroed_adrs_leaf_layer_forges_prob_one
  Qsag.tooth_zeroed_adrs_refutes_bound

#tooth_pair Qsag.symMerkleSuite_full_adaptive_forger_bound vs
  Qsag.tooth_zeroed_adrs_refutes_bound

end Qsag
end
