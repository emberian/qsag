module
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa
public import Qsag.Protocol.Signing.Fips205
import all Qsag.Protocol.Signing.Fips205
public import Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Protocol.Signing.HypertreeEufCma
public import Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity
import all Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity
public import Qsag.Protocol.Signing.ProdCollision
import all Qsag.Protocol.Signing.ProdCollision
public import Qsag.Protocol.Signing.SignatureOutputAndCacheLaws
import all Qsag.Protocol.Signing.SignatureOutputAndCacheLaws
public import Qsag.Protocol.Signing.ProdHashReductions
import all Qsag.Protocol.Signing.ProdHashReductions
public import Qsag.Protocol.Signing.HybridAddrPolicyAndFullPresetSecurity
import all Qsag.Protocol.Signing.HybridAddrPolicyAndFullPresetSecurity
import all Qsag.Math.Counting
import all Qsag.Oracle.Keccak
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Tests.SigningTeeth

Negative and mutation witnesses (`tooth_*`), toy fixtures and the inhabitedness witnesses that
evaluate the signing definitions on them, for the modules imported below, with the
`#tooth_pair`, `#verify_inhabited` and `#verify_constructive` audit lines that pair each of
them with the theorem it guards. The fixtures `crumbToySuite`, `prodToyStatefulParams`,
`prodToyForgery`, `zeroToySuite` and `zeroToyParams` are plain definitions and stay in the
library modules; every statement that evaluates a verifier or signer on them is here.
-/

/-! ## `Qsag.Protocol.Signing.Fips205` -/
public section
public section

namespace Qsag

set_option autoImplicit false

theorem tooth_slhDsaShake128s_m34_rejected :
    ({ slhDsaShake128s with m := 34 } : Fips205Params).wellFormed ≠ true := by
  decide

/-- Adding even one byte as an extra WOTS element is rejected before hashing. -/
theorem tooth_slh_trailing_wots_rejected (p : Fips205Params) (msg : List UInt8)
    (sig : SlhSignature) (pk : SlhPublicKey) (x : FipsXmssSig) (rest : List FipsXmssSig)
    (hLen : x.wotsSig.length = p.ell) :
    slhVerifyInternal p msg
      { sig with htSig := { x with wotsSig := x.wotsSig ++ [[0]] } :: rest } pk = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hs := (slhVerifyInternal_shapes p msg _ pk h).2.2.2.2
  simp only [List.all_cons, Bool.and_eq_true] at hs
  have hc := hs.1
  simp only [fipsXmssSigShape, Bool.and_eq_true, decide_eq_true_eq] at hc
  have bad := hc.1.1.1
  simp only [List.length_append, List.length_cons, List.length_nil, hLen] at bad
  omega

theorem tooth_sha3_256_category5_rejected (ctx digest : List UInt8) :
    encodePreHashMsgPrime slhDsaShake256f .sha3_256 ctx digest = none := by
  simp [encodePreHashMsgPrime, preHashCompatible, slhDsaShake256f, FipsPreHashAlg.securityBytes]

#tooth_pair Qsag.accepted_preHash_category vs Qsag.tooth_sha3_256_category5_rejected

#tooth_pair Qsag.fips205_wellFormed_exact_hMsg_bytes vs Qsag.tooth_slhDsaShake128s_m34_rejected

end Qsag

end
end

/-! ## `Qsag.Protocol.Signing.HashSigs` -/
public section
public section

namespace Qsag

set_option autoImplicit false

/-- Permissive small-`ell1` fast model test profiles (rejected by `productionWellFormed`). -/
def compactTestParams        : PqHashParams := ⟨4, 8, 2, 2, 4, 2, 4, false⟩

/-- Satisfiability witness: the checked signer succeeds on a concrete instance. -/
theorem evalStatelessCheckedSign_inhabited :
    (evalStatelessCheckedSign zeroToySuite zeroToyParams ⟨[], [], []⟩ [] [] 1).isSome = true := by
  decide +kernel

/-- `#tooth`: Toy 16-bit WOTS profiles (`ell1 = 8, w = 4`) pass permissive `wellFormed` for fast
    unit models, but are strictly rejected by `productionWellFormed`. -/
theorem tooth_productionWellFormed_rejects_short_wots :
    compactTestParams.wellFormed = true ∧ compactTestParams.productionWellFormed = false := by
  decide +kernel

/-- `#tooth`: Zero subtree height (`subtreeHeight = 0`) is rejected by `productionWellFormed`. -/
theorem tooth_productionWellFormed_rejects_zero_subtree_height :
    (⟨4, 128, 0, 1, 0, 0, 1, true⟩ : PqHashParams).productionWellFormed = false := by
  decide +kernel

/-- `#tooth`: Stateful profiles carrying non-zero FORS trees are rejected by `productionWellFormed`. -/
theorem tooth_productionWellFormed_rejects_stateful_with_fors :
    (⟨4, 128, 4, 2, 8, 4, 4, true⟩ : PqHashParams).productionWellFormed = false := by
  decide +kernel

/-- `#tooth`: Budgets exceeding `numLayers * subtreeHeight` or equal to `0` are rejected. -/
theorem tooth_productionWellFormed_rejects_invalid_budget :
    (⟨4, 128, 4, 2, 8, 4, 0, false⟩ : PqHashParams).productionWellFormed = false ∧
    (⟨4, 128, 4, 2, 8, 4, 9, false⟩ : PqHashParams).productionWellFormed = false := by
  decide +kernel

/-- `#tooth`: Relocating a stateless signature to a leaf other than the XOF-derived `derivedLeafIdx`
    is unconditionally rejected by `verifyProductionPqHashSig`. -/
theorem tooth_production_rejects_wrong_stateless_leaf
    (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) (leaf : Nat) (idxs : List Nat)
    (hD : deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot
            (thPreHash suite pk.pkSeed pk.pkRoot msg) = some (leaf, idxs))
    (hNe : sig.leafGlobalIdx ≠ leaf) :
    verifyProductionPqHashSig suite params pk msg sig = false := by
  obtain ⟨hWf, hSt, _⟩ := deriveProductionStatelessInputs_bounds _ _ _ _ _ _ _ _ hD
  rw [verifyProductionPqHashSig_eq]
  split
  · rfl
  · split
    · rfl
    · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
      split
      · rfl
      · rw [hD]; simp [hNe]

/-- `#tooth`: Non-zero `msgTswCtr` is unconditionally rejected by `verifyProductionPqHashSig`. -/
theorem tooth_production_rejects_nonzero_msgTswCtr
    (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) (hCtr : sig.msgTswCtr ≠ 0) :
    verifyProductionPqHashSig suite params pk msg sig = false := by
  rw [verifyProductionPqHashSig_eq]
  split
  · rfl
  · simp [hCtr]

/-- `#tooth`: FORS internal `.forsTree` Merkle nodes bind `keyPair = kp0` in `HashAdrs`, so
    distinct WOTS/FORS leaves `kp₁ ≠ kp₂ < 2^32` within the same bottom subtree produce
    disjoint preimages before hashing. -/
theorem tooth_production_fors_merkle_binds_kp0
    (pkSeed left right : List UInt8) (tree0 : UInt64) (kp₁ kp₂ h nodeIdx : Nat)
    (hKp1 : kp₁ < 2 ^ 32) (hKp2 : kp₂ < 2 ^ 32) (hNe : kp₁ ≠ kp₂) :
    thPreimage tagThH pkSeed ⟨0, tree0, .forsTree, UInt32.ofNat kp₁, UInt32.ofNat h, UInt32.ofNat nodeIdx⟩ [left, right] ≠
    thPreimage tagThH pkSeed ⟨0, tree0, .forsTree, UInt32.ofNat kp₂, UInt32.ofNat h, UInt32.ofNat nodeIdx⟩ [left, right] := by
  intro hEq
  have hAdrs := (thPreimage_injective hEq).2.2.1
  have hKpEq : (UInt32.ofNat kp₁).toNat = (UInt32.ofNat kp₂).toNat :=
    congrArg UInt32.toNat (congrArg HashAdrs.keyPair hAdrs)
  simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hKp1, Nat.mod_eq_of_lt hKp2] at hKpEq
  exact hNe hKpEq

theorem witness_production_parameter_profile : ∃ p, ProductionParameterProfile p :=
  ⟨corduroyCustody128Params, corduroyCustody128_productionWellFormed⟩

theorem tooth_short_model_is_not_production : ¬ ProductionParameterProfile compactTestParams := by
  intro h
  have hf := tooth_productionWellFormed_rejects_short_wots.2
  unfold ProductionParameterProfile at h
  rw [hf] at h
  cases h

theorem tooth_production_stateless_rejects_stateful (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (h : params.statefulJorts = true) :
    verifyProductionStatelessChecked suite params pk msg sig = false := by
  simp [verifyProductionStatelessChecked, h]

#tooth_pair Qsag.verifyProductionStatelessChecked_sound vs Qsag.tooth_production_stateless_rejects_stateful

end Qsag

end

#tooth_pair Qsag.production_profile_covers_full_digest vs Qsag.tooth_short_model_is_not_production

#verify_inhabited Qsag.production_profile_covers_full_digest Qsag.witness_production_parameter_profile
end

/-! ## `Qsag.Protocol.Signing.HypertreeEufCma` -/
public section
public section

namespace Qsag

set_option autoImplicit false

/-- Domain-separated concrete hash suite for `#tooth` executable verification:
    - `thPrfMsg` (`6` frames) maps `epoch = 0` (`bytes[88] = 0`) vs `epoch ≠ 0` (`bytes[88] ≠ 0`)
      to distinct `rRand` prefixes `[1, ...]` vs `[2, ...]`;
    - `thHashMsg` (`7` frames) maps `rRand[0] = 1, 2, 3` (`bytes[52]`) to three pairwise distinct
      128-crumb (`w = 4`) codewords `d₁ ≠ d₂`, `dStar ≠ d₁`, `dStar ≠ d₂`, all with target sum `192`
      and satisfying `min(d₁[r], d₂[r]) ≤ dStar[r]` for every `r < 128`! -/
def toothDistinctSuite : TweakableHashSuite where
  suiteId := []
  rawHash := fun bytes =>
    match bytes with
    | b :: _ =>
      if b == 6 then
        if bytes.getD 88 0 == 0 then
          [1] ++ List.replicate 31 0
        else
          [2] ++ List.replicate 31 0
      else if b == 7 then
        match bytes.getD 52 0 with
        | 1 => [0x0F, 0xF0] ++ List.replicate 30 0x1B
        | 2 => [0xF0, 0x0F] ++ List.replicate 30 0x1B
        | 3 => [0x66, 0x99] ++ List.replicate 30 0x1B
        | _ => List.replicate 32 0x1B
      else
        List.replicate 32 0x1B
    | [] => List.replicate 32 0x1B
  rawHash_len := fun bytes => by
    cases bytes with
    | nil => rfl
    | cons b bs =>
      dsimp only
      by_cases hb6 : b == 6
      · simp only [hb6, ↓reduceIte]
        split <;> rfl
      · simp only [hb6, Bool.false_eq_true, ↓reduceIte]
        by_cases hb7 : b == 7
        · simp only [hb7, ↓reduceIte]
          split <;> rfl
        · simp [hb7]

private theorem tagPrfMsg_bytes_eq :
    tagPrfMsg = [81, 83, 65, 71, 46, 80, 81, 46, 80, 82, 70, 77, 83, 71, 47, 118, 49] := by
  unfold tagPrfMsg
  rw [byteArray_toList_eq, String.toUTF8_eq_toByteArray]
  have hStr : "QSAG.PQ.PRFMSG/v1" =
      String.ofList ['Q', 'S', 'A', 'G', '.', 'P', 'Q', '.', 'P', 'R', 'F', 'M', 'S', 'G', '/', 'v', '1'] := by
    decide +kernel
  rw [hStr, String.toByteArray_ofList]
  decide +kernel

private theorem thPrfMsg_tooth_eq (skPrf optRand mu : List UInt8) :
    thPrfMsg toothDistinctSuite skPrf optRand mu =
      toothDistinctSuite.rawHash
        (encodeMultiFrame [[81, 83, 65, 71, 46, 80, 81, 46, 80, 82, 70, 77, 83, 71, 47, 118, 49],
          [], encodeAdrs zeroAdrs, skPrf, optRand, mu]) := by
  unfold thPrfMsg thCall thPreimage
  rw [tagPrfMsg_bytes_eq]
  rfl


/-- One layer of height one, one FORS tree of height one, `w = 4`, `ℓ₁ = 128`. -/
def crumbToyParams : PqHashParams := ⟨4, 128, 1, 1, 1, 1, 1, false⟩

/-- A well-shaped signature; under the constant suite it verifies for every message. -/
def crumbToyForgery : PqHashSig :=
  { rRand := [], msgTswCtr := 0, leafGlobalIdx := 0,
    forsOpenings := [⟨[], [[]]⟩],
    layerSigs := [⟨0, List.replicate 128 [], [[]]⟩] }

theorem crumbToyForgery_accepted :
    verifyPqHashSig crumbToySuite crumbToyParams
      (derivePublicKey crumbToySuite crumbToyParams ⟨[], [], []⟩) [] crumbToyForgery = true := by
  decide +kernel

/-- The premises of `hypertree_forgery_break_of_signingLog` hold on a concrete instance (empty
    query list), and there the ITSR branch is excluded, so a collision or preimage witness
    results; a constant hash is neither collision resistant nor one-way. -/
theorem hypertree_forgery_break_inhabited :
    SmTcrBreak crumbToySuite crumbToyParams ⟨[], [], []⟩ [] ∨
    PreimageBreak crumbToySuite crumbToyParams ⟨[], [], []⟩ [] [] crumbToyForgery := by
  rcases hypertree_forgery_break_of_signingLog crumbToySuite crumbToyParams ⟨[], [], []⟩ [] []
      crumbToyForgery (.inl ⟨rfl, rfl⟩) rfl (by decide) (fun _ he => by cases he)
      crumbToyForgery_accepted with h | h
  · exact absurd h (forsItsrBreak_empty_log _ _ _ _ _)
  · exact h

/-- The ITSR branch is inhabited on a genuine run: after one signing query on `[1]`, the same
    well-shaped signature on the unsigned message `[]` opens only FORS addresses already in the
    log (the constant suite sends both digests to the same leaf). -/
theorem forsItsrBreak_inhabited :
    ForsItsrBreak crumbToySuite crumbToyParams
      (derivePublicKey crumbToySuite crumbToyParams ⟨[], [], []⟩)
      (signingOracleLog crumbToySuite crumbToyParams ⟨[], [], []⟩ [⟨[1], [], 0, 1⟩])
      [] crumbToyForgery :=
  ⟨by decide +kernel, by decide, by decide +kernel⟩

/-- Concrete 1-layer stateful profile with budget `2 ^ 1 = 2` signatures (`maxSigsLog2 = 1`). -/
def toothStatefulParams : PqHashParams := ⟨4, 128, 1, 1, 0, 0, 1, true⟩

/-- **`#tooth` Concrete Executable Leaf-Reuse Forgery Witness
    (`tooth_mutantUncheckedReuseSign_concrete_forgery`)**:
    1. Real `checkedStatefulSignStep` strictly enforces the epoch budget (`2^1 = 2`) and aborts on
       epoch `2` with `.error (.budgetExhausted 2 2)` (and aborts on epoch-`0` equivocation with
       `.error (.equivocationRefused 0)`);
    2. `mutantUncheckedReuseSign` wraps `reqEpoch = 2` onto leaf `0`, emitting two valid signatures
       `sig₁` (on `m₁ = [1]`) and `sig₂` (on `m₂ = [2]`) with distinct codewords `dig₁ ≠ dig₂`;
    3. `forgeFromReusedLeafSigs` (using ONLY public inputs, zero `sk`) forges `sigStar` on fresh
       `msgStar = [3] ∉ [[1], [2]]` with a third distinct codeword `digStar` (`rStar = [3]`) passing
       `verifyCheckedStateful = true`, with every forged chain value equal to `honestChainNode`
       (`0` hash collisions) and `CheckedStatefulWotsTswWitness ... → False` (`0` backward inversions)! -/
theorem tooth_mutantUncheckedReuseSign_concrete_forgery :
    let suite := toothDistinctSuite
    let params := toothStatefulParams
    let sk : PqSecretKey := ⟨[], [], []⟩
    let pk := derivePublicKey suite params sk
    -- Real checked stateful oracle signs epochs 0 and 1, then aborts on epoch 2 (`budgetExhausted 2 2`)
    (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch
      [.signNext [1] 1, .signNext [9] 1, .signNext [2] 1]).abortError =
      some (.budgetExhausted 2 2) ∧
    -- Real checked stateful oracle also aborts on direct epoch-0 equivocation (`equivocationRefused 0`)
    (execCheckedStatefulOracle suite params sk initCheckedStatefulLatch
      [.signEpoch 0 [1] 1, .signEpoch 0 [2] 1]).abortError =
      some (.equivocationRefused 0) ∧
    -- Mutant signer succeeds on both `(reqEpoch = 0, [1])` and `(reqEpoch = 2, [2])` at leaf 0,
    -- and public `forgeFromReusedLeafSigs` forges fresh `msgStar = [3]` with 0 collisions & 0 inversions:
    ∃ st1 st2 sig₁ sig₂,
      mutantUncheckedReuseSign suite params sk initCheckedStatefulLatch 0 [1] 1 = .ok (st1, 0, [1], sig₁) ∧
      mutantUncheckedReuseSign suite params sk st1 2 [2] 1 = .ok (st2, 0, [2], sig₂) ∧
      [3] ∉ ([[1], [2]] : List (List UInt8)) ∧
      let sigStar := forgeFromReusedLeafSigs suite params pk [1] sig₁ [2] sig₂ [3] [3] 0
      let digStar := extractBaseWDigits params.w params.ell1
        (thHashMsg suite [3] pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot [3]) 0 0 0 0)
      verifyCheckedStateful suite params pk [3] sigStar = true ∧
      (∀ r, r < params.ell1 →
        (sigStar.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains.getD r [] =
          honestChainNode suite sk 0 0 0 r (digStar.getD r 0)) ∧
      (CheckedStatefulWotsTswWitness suite params sk [(0, [1], sig₁), (0, [2], sig₂)] [3] sigStar → False) := by
  intro suite params sk pk
  refine ⟨?_, ?_, ?_⟩
  · simp only [suite, params, sk, execCheckedStatefulOracle, execCheckedStatefulOracleAux,
               checkedStatefulSignStep, checkedStatefulFreshEpochSign, evalSingleSign, thPrfMsg_tooth_eq]
    decide +kernel
  · simp only [suite, params, sk, execCheckedStatefulOracle, execCheckedStatefulOracleAux,
               checkedStatefulSignStep, checkedStatefulFreshEpochSign, evalSingleSign, thPrfMsg_tooth_eq]
    decide +kernel
  · cases hM1 : mutantUncheckedReuseSign suite params sk
        initCheckedStatefulLatch 0 [1] 1 with
    | error e =>
      exfalso
      have hOk1 : (mutantUncheckedReuseSign suite params sk
          initCheckedStatefulLatch 0 [1] 1).isOk = true := by
        dsimp only [suite, params, sk]
        unfold mutantUncheckedReuseSign evalSingleSign
        simp only [thPrfMsg_tooth_eq]
        decide +kernel
      rw [hM1] at hOk1; cases hOk1
    | ok q1 =>
      rcases q1 with ⟨st1, leaf1, m1Out, sig₁⟩
      cases hM2 : mutantUncheckedReuseSign suite params sk
          st1 2 [2] 1 with
      | error e =>
        exfalso
        have hOk2 : (match mutantUncheckedReuseSign suite params sk
            initCheckedStatefulLatch 0 [1] 1 with
          | .error _ => false
          | .ok (s1, _, _, _) =>
            (mutantUncheckedReuseSign suite params sk s1 2 [2] 1).isOk) = true := by
          dsimp only [suite, params, sk]
          unfold mutantUncheckedReuseSign evalSingleSign
          simp only [thPrfMsg_tooth_eq]
          decide +kernel
        rw [hM1] at hOk2; dsimp only at hOk2; rw [hM2] at hOk2; cases hOk2
      | ok q2 =>
        rcases q2 with ⟨st2, leaf2, m2Out, sig₂⟩
        have hTV : toothStatefulParams.checkedStatefulValid = true := by decide +kernel
        have hL1AndIdx : leaf1 = 0 ∧ m1Out = [1] ∧ sig₁.leafGlobalIdx = 0 := by
          have hM1' := hM1
          dsimp only [suite, params, sk] at hM1'
          unfold mutantUncheckedReuseSign at hM1'
          rw [hTV] at hM1'
          dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hM1'
          cases hE1 : evalSingleSign toothDistinctSuite toothStatefulParams ⟨[], [], []⟩ [1]
              (buildStatefulDetOptDomain 0 []) (0 % 2 ^ toothStatefulParams.maxSigsLog2) 1 with
          | none => rw [hE1] at hM1'; cases hM1'
          | some s =>
            rw [hE1] at hM1'
            injection hM1' with hT
            rcases Prod.mk.inj hT with ⟨_, hTb⟩
            rcases Prod.mk.inj hTb with ⟨hLeaf, hTc⟩
            rcases Prod.mk.inj hTc with ⟨hMsg, hS⟩
            subst s
            have hInv := (evalSingleSign_stateful_inv toothDistinctSuite toothStatefulParams ⟨[], [], []⟩ [1]
              (buildStatefulDetOptDomain 0 []) (0 % 2 ^ toothStatefulParams.maxSigsLog2) 1 sig₁ rfl hE1).2.2.2.2.1
            exact ⟨hLeaf.symm, hMsg.symm, hInv⟩
        have hL2 : leaf2 = 0 ∧ m2Out = [2] := by
          have hM2' := hM2
          dsimp only [suite, params, sk] at hM2'
          unfold mutantUncheckedReuseSign at hM2'
          rw [hTV] at hM2'
          dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hM2'
          cases hE2 : evalSingleSign toothDistinctSuite toothStatefulParams ⟨[], [], []⟩ [2]
              (buildStatefulDetOptDomain 2 []) (2 % 2 ^ toothStatefulParams.maxSigsLog2) 1 with
          | none => rw [hE2] at hM2'; cases hM2'
          | some s =>
            rw [hE2] at hM2'
            injection hM2' with hT
            rcases Prod.mk.inj hT with ⟨_, hTb⟩
            rcases Prod.mk.inj hTb with ⟨hLeaf, hTc⟩
            exact ⟨hLeaf.symm, (Prod.mk.inj hTc).1.symm⟩
        rcases hL1AndIdx with ⟨rfl, rfl, hSig1Idx⟩
        rcases hL2 with ⟨rfl, rfl⟩
        have hTsw3 :
            let pk0 := derivePublicKey suite params sk
            let leaf := sig₁.leafGlobalIdx
            let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
            let kp0 := leaf % 2 ^ params.subtreeHeight
            checkTargetSum params.w params.ell1 params.targetSum
              (extractBaseWDigits params.w params.ell1
                (thHashMsg suite [3] pk0.pkSeed pk0.pkRoot
                  (thPreHash suite pk0.pkSeed pk0.pkRoot [3]) 0 tree0 (UInt32.ofNat kp0) 0)) = true := by
          dsimp only [suite, params, sk]
          rw [hSig1Idx]
          decide +kernel
        have hDom3 :
            let pk0 := derivePublicKey suite params sk
            let leaf := sig₁.leafGlobalIdx
            let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
            let kp0 := leaf % 2 ^ params.subtreeHeight
            let dig₁ := extractBaseWDigits params.w params.ell1
              (thHashMsg suite sig₁.rRand pk0.pkSeed pk0.pkRoot
                (thPreHash suite pk0.pkSeed pk0.pkRoot [1]) 0 tree0 (UInt32.ofNat kp0)
                (sig₁.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
            let dig₂ := extractBaseWDigits params.w params.ell1
              (thHashMsg suite sig₂.rRand pk0.pkSeed pk0.pkRoot
                (thPreHash suite pk0.pkSeed pk0.pkRoot [2]) 0 tree0 (UInt32.ofNat kp0)
                (sig₂.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
            let digStar := extractBaseWDigits params.w params.ell1
              (thHashMsg suite [3] pk0.pkSeed pk0.pkRoot
                (thPreHash suite pk0.pkSeed pk0.pkRoot [3]) 0 tree0 (UInt32.ofNat kp0) 0)
            ∀ r, r < params.ell1 →
              dig₁.getD r 0 ≤ digStar.getD r 0 ∨ dig₂.getD r 0 ≤ digStar.getD r 0 := by
          have hDecDom :
              (match mutantUncheckedReuseSign suite params sk
                       initCheckedStatefulLatch 0 [1] 1,
                     mutantUncheckedReuseSign suite params sk
                       st1 2 [2] 1 with
               | .ok (_, _, _, s1), .ok (_, _, _, s2) =>
                 let pk0 := derivePublicKey suite params sk
                 let leaf := s1.leafGlobalIdx
                 let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
                 let kp0 := leaf % 2 ^ params.subtreeHeight
                 let d1 := extractBaseWDigits params.w params.ell1
                   (thHashMsg suite s1.rRand pk0.pkSeed pk0.pkRoot
                     (thPreHash suite pk0.pkSeed pk0.pkRoot [1]) 0 tree0 (UInt32.ofNat kp0)
                     (s1.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
                 let d2 := extractBaseWDigits params.w params.ell1
                   (thHashMsg suite s2.rRand pk0.pkSeed pk0.pkRoot
                     (thPreHash suite pk0.pkSeed pk0.pkRoot [2]) 0 tree0 (UInt32.ofNat kp0)
                     (s2.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
                 let dS := extractBaseWDigits params.w params.ell1
                   (thHashMsg suite [3] pk0.pkSeed pk0.pkRoot
                     (thPreHash suite pk0.pkSeed pk0.pkRoot [3]) 0 tree0 (UInt32.ofNat kp0) 0)
                 (List.range params.ell1).all (fun r => decide (d1.getD r 0 ≤ dS.getD r 0 ∨ d2.getD r 0 ≤ dS.getD r 0))
               | _, _ => false) = true := by
            have hClosed :
                (match mutantUncheckedReuseSign suite params sk
                         initCheckedStatefulLatch 0 [1] 1 with
                 | .ok (s1State, _, _, s1) =>
                   match mutantUncheckedReuseSign suite params sk
                           s1State 2 [2] 1 with
                   | .ok (_, _, _, s2) =>
                     let pk0 := derivePublicKey suite params sk
                     let leaf := s1.leafGlobalIdx
                     let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
                     let kp0 := leaf % 2 ^ params.subtreeHeight
                     let d1 := extractBaseWDigits params.w params.ell1
                       (thHashMsg suite s1.rRand pk0.pkSeed pk0.pkRoot
                         (thPreHash suite pk0.pkSeed pk0.pkRoot [1]) 0 tree0 (UInt32.ofNat kp0)
                         (s1.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
                     let d2 := extractBaseWDigits params.w params.ell1
                       (thHashMsg suite s2.rRand pk0.pkSeed pk0.pkRoot
                         (thPreHash suite pk0.pkSeed pk0.pkRoot [2]) 0 tree0 (UInt32.ofNat kp0)
                         (s2.layerSigs.getD 0 ⟨0, [], []⟩).tswCtr)
                     let dS := extractBaseWDigits params.w params.ell1
                       (thHashMsg suite [3] pk0.pkSeed pk0.pkRoot
                         (thPreHash suite pk0.pkSeed pk0.pkRoot [3]) 0 tree0 (UInt32.ofNat kp0) 0)
                     (List.range params.ell1).all (fun r => decide (d1.getD r 0 ≤ dS.getD r 0 ∨ d2.getD r 0 ≤ dS.getD r 0))
                   | .error _ => false
                 | .error _ => false) = true := by
              dsimp only [suite, params, sk]
              unfold mutantUncheckedReuseSign evalSingleSign
              simp only [thPrfMsg_tooth_eq]
              decide +kernel
            rw [hM1] at hClosed ⊢
            dsimp only at hClosed ⊢
            rw [hM2] at hClosed ⊢
            exact hClosed
          rw [hM1, hM2] at hDecDom
          dsimp only at hDecDom ⊢
          intro r hr
          have hAll := List.all_eq_true.mp hDecDom r (List.mem_range.mpr hr)
          exact of_decide_eq_true hAll
        obtain ⟨hVerStar, hChainsStar, hNoWots⟩ :=
          mutantUncheckedReuseSign_collision_free_forgery suite params sk
            [3] [3] 0 hM1 hM2 (by decide) hTsw3 hDom3
        refine ⟨st1, st2, sig₁, sig₂, ?_⟩
        refine ⟨rfl, hM2, by decide, ?_⟩
        intro sigStar digStar
        have hPk : derivePublicKey suite params sk = pk := rfl
        have hSigStar : forgeFromReusedLeafSigs suite params pk [1] sig₁ [2] sig₂ [3] [3] 0 = sigStar := rfl
        have hDigStar :
            extractBaseWDigits params.w params.ell1
              (thHashMsg suite [3] pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot [3]) 0 0 0 0) =
              digStar := rfl
        rw [hPk, hSigStar] at hVerStar
        have hParams1 : params.numLayers = 1 := rfl
        have hNoWots' := hNoWots hParams1
        rw [hPk, hSigStar] at hNoWots'
        refine ⟨hVerStar, ?_, hNoWots'⟩
        intro r hr
        have hC := hChainsStar r hr
        have hZeroDiv : 0 / 2 ^ params.subtreeHeight = 0 := Nat.zero_div _
        have hZeroMod : 0 % 2 ^ params.subtreeHeight = 0 := Nat.zero_mod _
        have hU64 : UInt64.ofNat 0 = (0 : UInt64) := rfl
        have hU32 : UInt32.ofNat 0 = (0 : UInt32) := rfl
        rw [hPk, hSigStar, hSig1Idx, hZeroDiv, hZeroMod, hU64, hU32, hDigStar] at hC
        exact hC

/-- Concrete 2-layer (`d = 2`) stateful profile with budget `2 ^ 2 = 4` signatures (`maxSigsLog2 = 2`). -/
def inhabitedStatefulParams : PqHashParams := ⟨4, 128, 1, 2, 0, 0, 2, true⟩

/-- Multi-turn checked stateful query schedule exercising fresh `.signNext` across subtree
    boundaries (`epoch = 0, 1`), crash-recovery `.retryEpoch 1`, and explicit `.signEpoch 2`. -/
def inhabitedStatefulQueries : List CheckedStatefulQuery :=
  [.signNext [10] 1, .signNext [20] 1, .retryEpoch 1 [20], .signEpoch 2 [30] 1]

/-- Well-shaped 2-layer signature on leaf `0` accepted by `verifyCheckedStateful` under `crumbToySuite`. -/
def inhabitedStatefulForgery : PqHashSig :=
  { rRand := []
    msgTswCtr := 0
    leafGlobalIdx := 0
    forsOpenings := []
    layerSigs := [⟨0, List.replicate 128 [], [[]]⟩, ⟨0, List.replicate 128 [], [[]]⟩] }

/-- **Inhabited Multi-Signature Constructive Extraction Witness (`inhabited_checked_stateful_multi_sign_extract`)**:
    Directly executes `checked_stateful_hypertree_euf_cma_extract` on the 4-entry, 2-layer
    multi-signature transcript produced by `inhabitedStatefulQueries` (`0 Classical.choice`). -/
def inhabited_checked_stateful_multi_sign_extract :
    let log := (execCheckedStatefulOracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
                  initCheckedStatefulLatch inhabitedStatefulQueries).emittedLog
    PSum (CheckedStatefulCollisionWitness crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩ log)
         (CheckedStatefulWotsTswWitness crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩ log
            [99] inhabitedStatefulForgery) :=
  checked_stateful_hypertree_euf_cma_extract
    crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
    inhabitedStatefulQueries [99] inhabitedStatefulForgery
    (.inl ⟨rfl, rfl⟩)
    (by decide +kernel)
    (by decide +kernel)

/-- **Multi-Signature Inhabitedness Theorem (`inhabited_checked_stateful_multi_sign_log`)**:
    Proves that all hypotheses of `checked_stateful_hypertree_euf_cma_extract` and
    `checked_stateful_strict_euf_cma_extract` are jointly inhabited on a genuine 2-layer (`d = 2`),
    multi-signature checked stateful execution:
    1. `execCheckedStatefulStrict` succeeds (`abortError = none`) with `stFinal.nextEpoch = 3` and
       `4` emitted log entries across epochs `[0, 1, 1, 2]` and messages `[[10], [20], [20], [30]]`;
    2. Every emitted signature passes `verifyCheckedStateful = true`;
    3. `msgStar = [99]` is fresh (`∉ log.map (·.2.1)`) and `inhabitedStatefulForgery` passes
       `verifyCheckedStateful = true`; and
    4. `checked_stateful_hypertree_euf_cma_extract` produces an inhabited transcript-indexed break witness! -/
theorem inhabited_checked_stateful_multi_sign_log :
    let suite := crumbToySuite
    let params := inhabitedStatefulParams
    let sk : PqSecretKey := ⟨[], [], []⟩
    let pk := derivePublicKey suite params sk
    let run := execCheckedStatefulOracle suite params sk initCheckedStatefulLatch inhabitedStatefulQueries
    run.abortError = none ∧
    (∃ stFinal, execCheckedStatefulStrict suite params sk initCheckedStatefulLatch inhabitedStatefulQueries =
      .ok (stFinal, run.emittedLog) ∧ stFinal.nextEpoch = 3) ∧
    run.emittedLog.length = 4 ∧
    (run.emittedLog.map Prod.fst) = [0, 1, 1, 2] ∧
    (run.emittedLog.map fun e => e.2.1) = [[10], [20], [20], [30]] ∧
    (∀ e ∈ run.emittedLog, verifyCheckedStateful suite params pk e.2.1 e.2.2 = true) ∧
    ([99] : List UInt8) ∉ (run.emittedLog.map fun e => e.2.1) ∧
    verifyCheckedStateful suite params pk [99] inhabitedStatefulForgery = true ∧
    (Nonempty (CheckedStatefulCollisionWitness suite params sk run.emittedLog) ∨
     Nonempty (CheckedStatefulWotsTswWitness suite params sk run.emittedLog [99] inhabitedStatefulForgery)) := by
  dsimp only
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel, ?_,
          by decide +kernel, by decide +kernel, ?_⟩
  · cases hStr : execCheckedStatefulStrict crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
        initCheckedStatefulLatch inhabitedStatefulQueries with
    | error err =>
      exfalso
      have hOk : (execCheckedStatefulStrict crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
          initCheckedStatefulLatch inhabitedStatefulQueries).isOk = true := by decide +kernel
      rw [hStr] at hOk; cases hOk
    | ok pair =>
      rcases pair with ⟨stFinal, log⟩
      have hOrcEq :=
        ((execCheckedStatefulStrict_eq_oracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
          inhabitedStatefulQueries initCheckedStatefulLatch).1 stFinal log).mp hStr
      have hLogEq : log = (execCheckedStatefulOracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
          initCheckedStatefulLatch inhabitedStatefulQueries).emittedLog :=
        congrArg CheckedStatefulOracleRun.emittedLog hOrcEq.symm
      have hNext : stFinal.nextEpoch = 3 := by
        have hDec : (match execCheckedStatefulStrict crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
                        initCheckedStatefulLatch inhabitedStatefulQueries with
                     | .ok (s, _) => s.nextEpoch == 3
                     | .error _ => false) = true := by decide +kernel
        rw [hStr] at hDec
        exact of_decide_eq_true (by simpa [beq_iff_eq] using hDec)
      exact ⟨stFinal, by rw [← hLogEq], hNext⟩
  · intro e he
    exact checkedStatefulOracle_accepts crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
      inhabitedStatefulQueries he
  · cases inhabited_checked_stateful_multi_sign_extract with
    | inl col => exact .inl ⟨col⟩
    | inr wots => exact .inr ⟨wots⟩

/-- The latch invariant has a concrete occupied state, not just an empty log. -/
theorem witness_occupied_epoch_latch : ∃ st : EpochLatchState, st.WellFormed := by
  refine ⟨⟨1, some (0, [], ⟨[], 0, 0, [], []⟩)⟩, ?_⟩
  intro ep msg sig h
  change some (0, [], (⟨[], 0, 0, [], []⟩ : PqHashSig)) = some (ep, msg, sig) at h
  have he := congrArg (fun x => x.1) (Option.some.inj h)
  change 0 = ep at he
  change ep < 1
  omega

/-- The invariant and an actual successful replay share one assignment. -/
theorem witness_occupied_epoch_latch_step :
    ∃ (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
      (st : EpochLatchState) (sig : PqHashSig),
      st.WellFormed ∧ epochLatchSign suite params sk [] 0 st 0 [] = some (st, sig) := by
  refine ⟨crumbToySuite, inhabitedStatefulParams, ⟨[], [], []⟩,
    ⟨1, some (0, [], ⟨[], 0, 0, [], []⟩)⟩, ⟨[], 0, 0, [], []⟩, ?_, ?_⟩
  · intro ep msg sig h
    have he := congrArg (fun x => x.1) (Option.some.inj h)
    change 0 = ep at he
    change ep < 1
    omega
  · exact stateful_jorts_crash_retry_idempotent _ _ _ _ _ _ _ _

/-- Equivocation rejection with the occupied latch explicit in the theorem statement. -/
theorem tooth_occupied_latch_rejects_equivocation
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (optRand : List UInt8) (maxGrind ep : Nat)
    (msg msg' : List UInt8) (sig : PqHashSig) (hDiff : msg' ≠ msg) :
    epochLatchSign suite params sk optRand maxGrind
      ⟨ep + 1, some (ep, msg, sig)⟩ ep msg' = none :=
  stateful_jorts_equivocation_rejected suite params sk optRand maxGrind ep msg msg' sig hDiff

theorem prodToyForgery_accepted :
    verifyProductionPqHashSig crumbToySuite prodToyStatefulParams
      (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩) [] prodToyForgery = true := by
  decide +kernel

/-- The premises of `production_stateful_forgery_break` hold jointly on a concrete instance: the
    constant suite accepts a well-shaped production signature with nothing signed. -/
theorem witness_production_stateful_forgery :
    ∃ sigStar : PqHashSig,
      (prodToyStatefulParams.w = 4 ∨ prodToyStatefulParams.w = 16) ∧
      prodToyStatefulParams.statefulJorts = true ∧
      (∀ q, q ∈ ([] : List ProdSigningQuery) → ∀ q', q' ∈ ([] : List ProdSigningQuery) →
        q.epoch = q'.epoch → q = q') ∧
      (∀ e ∈ productionSigningLog crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [],
        e.1 ≠ ([] : List UInt8)) ∧
      verifyProductionPqHashSig crumbToySuite prodToyStatefulParams
        (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩) [] sigStar = true :=
  ⟨prodToyForgery, .inl rfl, rfl, (fun _ h => by cases h), (fun _ h => by cases h),
    prodToyForgery_accepted⟩

/-- On that instance the reduction returns a break of the constant hash. -/
theorem production_forgery_break_inhabited :
    ProdSmTcrBreak crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] ∨
    ProdPreimageBreak crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] [] prodToyForgery :=
  production_stateful_forgery_break crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] []
    prodToyForgery (.inl rfl) rfl (fun _ h => by cases h) (fun _ h => by cases h)
    prodToyForgery_accepted

end Qsag

end

#tooth_pair Qsag.stateful_jorts_crash_retry_idempotent vs Qsag.tooth_occupied_latch_rejects_equivocation

#verify_inhabited Qsag.epochLatchSign_preserves_wellFormed Qsag.witness_occupied_epoch_latch_step

#verify_inhabited Qsag.production_stateful_forgery_break Qsag.witness_production_stateful_forgery
end

/-! ## `Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity` -/
public section
public section

namespace Qsag

set_option autoImplicit false

set_option exponentiation.threshold 2048

attribute [local irreducible] frontierSubCount frontierDecCount

def verifyFrontierFtsNoTargetSum (H : FrontierHashSuite) (p : FrontierFtsParams)
    (pk : FrontierPublicKey) (frontier offs : List Nat) (chainVals : List (BitVec 256)) : Bool :=
  if chainVals.length != p.frontierLen || offs.length != p.frontierLen then false
  else if offs.any (fun a => decide (p.winternitzW ≤ a)) then false
  else match runFrontierStackLoop H pk.pkSeed p.winternitzW frontier offs chainVals [] with
    | [(1, rootOut)] => decide (rootOut = pk.root)
    | _ => false

theorem tooth_drop_target_sum_allows_one_sig_forgery
    (H : FrontierHashSuite) (p : FrontierFtsParams) (hw : 2 ≤ p.winternitzW) (hL : 2 ≤ p.frontierLen)
    (sk : FrontierSecretKey) (tr : AntichainTree) (hVal : tr.Valid p.treeHeight = true) (hSz : tr.size = p.frontierLen) :
    ∃ (offs₁ offs₂ : List Nat) (forgedVals : List (BitVec 256)),
      offs₂ ≠ offs₁ ∧
      verifyFrontierFtsNoTargetSum H p (deriveFrontierPk H p sk) (tr.frontierNodes 1) offs₂ forgedVals = true := by
  let pk := deriveFrontierPk H p sk
  let offs₁ := List.replicate p.frontierLen 0
  let honestVals := honestSignSubtree H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs₁
  let v₀ := (tr.frontierNodes 1).headD 2
  let forgedVals := (H.chainStep pk.pkSeed v₀ 0 (honestVals.headD 0#256)) :: honestVals.tail
  let offs₂ := 1 :: List.replicate (p.frontierLen - 1) 0
  have hNe : offs₂ ≠ offs₁ := by
    dsimp only [offs₁, offs₂]
    cases hFL : p.frontierLen with
    | zero => omega
    | succ m => simp [List.replicate_succ]
  refine ⟨offs₁, offs₂, forgedVals, hNe, ?_⟩
  have hHLen : honestVals.length = p.frontierLen :=
    (honestSignSubtree_length H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs₁ hVal).trans hSz
  have hNLen := (tr.frontierNodes_length 1).trans hSz
  have hOLen₁ : offs₁.length = p.frontierLen := List.length_replicate
  have hOLen₂ : offs₂.length = p.frontierLen := by dsimp only [offs₂]; rw [List.length_cons, List.length_replicate]; omega
  cases hFN : tr.frontierNodes 1 with
  | nil => rw [hFN] at hNLen; change 0 = p.frontierLen at hNLen; omega
  | cons u us =>
    cases hHV : honestVals with
    | nil => rw [hHV] at hHLen; change 0 = p.frontierLen at hHLen; omega
    | cons x xs =>
      have hFLS : p.frontierLen = us.length + 1 := by rw [hFN] at hNLen; exact hNLen.symm
      have hO₁ : offs₁ = 0 :: List.replicate us.length 0 := by dsimp only [offs₁]; rw [hFLS, List.replicate_succ]
      have hO₂ : offs₂ = 1 :: List.replicate us.length 0 := by dsimp only [offs₂]; rw [hFLS, Nat.add_sub_cancel]
      have hFLen : forgedVals.length = p.frontierLen := by
        dsimp only [forgedVals]; rw [hHV]; rw [hHV] at hHLen; exact hHLen
      have hNoBig : offs₂.any (fun a => decide (p.winternitzW ≤ a)) = false := by
        rw [hO₂, List.any_cons, decide_eq_false (by omega : ¬ p.winternitzW ≤ 1)]
        suffices (List.replicate us.length 0).any (fun a => decide (p.winternitzW ≤ a)) = false by rw [this]; rfl
        apply List.any_eq_false.mpr
        intro a ha
        rw [List.mem_replicate] at ha
        simp only [ha.2, decide_eq_true_eq]
        omega
      change verifyFrontierFtsNoTargetSum H p pk (u :: us) offs₂ forgedVals = true
      unfold verifyFrontierFtsNoTargetSum
      have hLenChk : (forgedVals.length != p.frontierLen || offs₂.length != p.frontierLen) = false := by
        rw [hFLen, hOLen₂]; simp
      simp only [hLenChk, hNoBig, Bool.false_eq_true, ↓reduceIte]
      have hStepEq : runFrontierStackLoop H pk.pkSeed p.winternitzW (u :: us) offs₂ forgedVals [] =
          runFrontierStackLoop H pk.pkSeed p.winternitzW (tr.frontierNodes 1) offs₁ honestVals [] := by
        dsimp only [forgedVals, v₀]; rw [hFN, hHV, hO₁, hO₂]; unfold runFrontierStackLoop
        simp only [List.headD_cons, List.tail_cons, Nat.sub_zero]
        have hAdv : chainAdvance H pk.pkSeed u 0 (p.winternitzW - 1) x =
            chainAdvance H pk.pkSeed u 1 (p.winternitzW - 1 - 1) (H.chainStep pk.pkSeed u 0 x) := by
          conv => lhs; rw [show p.winternitzW - 1 = (p.winternitzW - 1 - 1) + 1 by omega]
          rfl
        rw [hAdv]
      rw [hStepEq]
      have hLp := runFrontierStackLoop_tree_eq H pk.pkSeed p.winternitzW tr 1 offs₁ honestVals
        [] [] [] [] (by decide) (hOLen₁.trans hSz.symm) (hHLen.trans hSz.symm)
      simp only [List.append_nil] at hLp; rw [hLp]; unfold runFrontierStackLoop collapseFrontierStack
      rw [evalAntichainTree_honest H pk.pkSeed sk.skSeed p.winternitzW (by omega) p.treeHeight 1 tr offs₁
        (by decide) hVal (hOLen₁.trans hSz.symm)
        (fun a ha => by rw [List.mem_replicate] at ha; rw [ha.2]; omega)
        (fun hLf => by subst hLf; unfold AntichainTree.size at hSz; omega)]
      simp [pk, deriveFrontierPk]

theorem tooth_static_key_compromise_forges_historical_epoch
    (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hBytes : p.nodeBytes = 32) (hUses : p.maxSafeUses = 1)
    (hw : 1 ≤ p.winternitzW) (hL : 2 ≤ p.frontierLen)
    (hDom : 2 ^ 256 ≤ frontierRootSubCount p.treeHeight p.frontierLen *
                      frontierDecCount p.winternitzW p.frontierLen p.targetSum)
    (voteHash : EpochVoteHasher) (chainId : BitVec 256)
    (skStatic : FrontierSecretKey) (hedge : BitVec 256)
    (honestDigest forgedDigest : BitVec 256) (hDiff : forgedDigest ≠ honestDigest) :
    ∃ forgedVote : RotatedEpochVote,
      forgedVote.voteDigest = forgedDigest ∧ forgedVote.voteDigest ≠ honestDigest ∧
      verifyRotatedEpochVote H p voteHash chainId (deriveFrontierPk H p skStatic) 0 forgedDigest forgedVote =
        some (deriveFrontierPk H p skStatic) := by
  let pk₀ := deriveFrontierPk H p skStatic
  let msg := voteHash chainId 0 forgedDigest pk₀.root
  let d := H.prehashMsg pk₀.pkSeed pk₀.root msg
  let rand := H.prfRand skStatic.skPrf pk₀.pkSeed pk₀.root hedge d
  let rk := (H.squeezeRank pk₀.pkSeed pk₀.root rand d 0).toNat
  obtain ⟨tr, _, offs, hUnr, _, _, _, _, _, _, _, _⟩ :=
    unrankFrontierFts_bijective p rk (Nat.lt_of_lt_of_le (H.squeezeRank pk₀.pkSeed pk₀.root rand d 0).isLt hDom)
  have hCtr0 : ¬ ((0 : UInt16).toNat >= 2 ^ p.counterBits) := by
    have hPow : 0 < 2 ^ p.counterBits := Nat.pow_pos (by decide : 0 < 2)
    change ¬ (0 >= 2 ^ p.counterBits); omega
  let sig : FrontierSignature := ⟨rand, 0, honestSignSubtree H pk₀.pkSeed skStatic.skSeed p.winternitzW p.treeHeight 1 tr offs⟩
  have hSign : signFrontierFts H p skStatic hedge 0 msg = some sig := by
    unfold signFrontierFts
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hCtr0 h))]
    simp [pk₀, msg, d, rand, rk, hUnr, sig]
  refine ⟨⟨⟨0, pk₀.root⟩, forgedDigest, sig⟩, rfl, hDiff, ?_⟩
  unfold verifyRotatedEpochVote
  have hC1 : (p.nodeBytes != 32 || p.maxSafeUses != 1) = false := by rw [hBytes, hUses]; rfl
  have hC2 : ((0 : UInt64) != 0 || (0 : UInt64).toNat + 1 >= 2 ^ 64) = false := by decide +kernel
  have hC3 : (forgedDigest != forgedDigest) = false := by simp
  simp only [hC1, hC2, hC3, Bool.false_eq_true, ↓reduceIte]
  rw [verifyFrontierFts_signFrontierFts H p hw hL skStatic hedge 0 msg sig hSign]
  simp [pk₀, deriveFrontierPk]

theorem tooth_corduroy_t_corrupted_custodians_uniquely_pin_secret
    (P Q : List Goldilocks)
    (hP : verifyShamirPolyConsistent 2 P [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] = true)
    (hQ : verifyShamirPolyConsistent 2 Q [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] = true) :
    ∃ sPinned : Goldilocks,
      sPinned ≠ Goldilocks.zero ∧
      RoundPoly.evalCoeffs P Goldilocks.zero = sPinned ∧
      RoundPoly.evalCoeffs Q Goldilocks.zero = sPinned := by
  have hRef : verifyShamirPolyConsistent 2 [Goldilocks.ofNat 1, Goldilocks.ofNat 4]
      [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] = true := by decide +kernel
  have hEqQ := shamirPolyConsistent_unique_at_zero 2 P Q [Goldilocks.ofNat 1, Goldilocks.ofNat 2]
    [Goldilocks.ofNat 5, Goldilocks.ofNat 9] (by decide +kernel) (by decide) hP hQ
  have hEqRef := shamirPolyConsistent_unique_at_zero 2 P [Goldilocks.ofNat 1, Goldilocks.ofNat 4]
    [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] (by decide +kernel) (by decide) hP hRef
  exact ⟨RoundPoly.evalCoeffs P Goldilocks.zero, by rw [hEqRef]; decide +kernel, rfl, hEqQ.symm⟩

attribute [local irreducible] evalFtsCshake256_32 cshakeEpochVoteHasher

theorem witness_compact1122_forgery :
    ∃ (H : FrontierHashSuite) (p : FrontierFtsParams) (_ : 2 ≤ p.frontierLen)
      (sk : FrontierSecretKey) (hedge₁ : BitVec 256) (ctr₁ : UInt16)
      (m₁ : List UInt8) (sig₁ : FrontierSignature),
      signFrontierFts H p sk hedge₁ ctr₁ m₁ = some sig₁ ∧
      ∃ (m₂ : List UInt8) (sig₂ : FrontierSignature),
        m₂ ≠ m₁ ∧ verifyFrontierFts H p (deriveFrontierPk H p sk) m₂ sig₂ = true :=
  ⟨witCompact1122H, compact1122Params, witCompact1122_hL, witCompact1122Sk, 0#256, 0, [1], witCompact1122Sig,
    witCompact1122_hSign, [2], witCompact1122Sig, witCompact1122_hNe, witCompact1122_hVer⟩

