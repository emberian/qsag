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

theorem witness_rotatedEpochVote_chain :
    ∃ (H : FrontierHashSuite) (p : FrontierFtsParams) (_ : 2 ≤ p.frontierLen)
      (voteHash : EpochVoteHasher) (chainId pkSeed : BitVec 256) (startEp : Nat)
      (histRecords : List HonestEpochRecord) (advDigests : List (BitVec 256))
      (advVotes : List RotatedEpochVote) (anchorPk finalPk : FrontierPublicKey)
      (hLen1 : histRecords.length = advDigests.length) (hLen2 : advDigests.length = advVotes.length),
      (∀ idx : Fin histRecords.length, (histRecords.get idx).ValidAt H p voteHash chainId pkSeed (startEp + idx.1)) ∧
      (∀ r₀, histRecords.head? = some r₀ → anchorPk = deriveFrontierPk H p r₀.sk) ∧
      (∀ i : Fin histRecords.length, ∀ rNext, histRecords[i.1 + 1]? = some rNext →
        (histRecords.get i).nextPkRoot = (deriveFrontierPk H p rNext.sk).root) ∧
      verifyRotatedEpochChain H p voteHash chainId anchorPk startEp advDigests advVotes = some finalPk ∧
      (∃ i : Fin histRecords.length,
        advDigests.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 hLen1⟩ ≠ (histRecords.get i).voteDigest ∨
        (advVotes.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 (hLen1.trans hLen2)⟩).link.nextEpochPkRoot ≠ (histRecords.get i).nextPkRoot) :=
  ⟨witEpochH, compact1122Params, witCompact1122_hL, cshakeEpochVoteHasher, 0#256, 3#256, 0,
    [witEpochRec0], [1#256], [witEpochAdvV], witEpochPk, ⟨3#256, 0#256⟩, rfl, rfl,
    witEpoch_hVal, witEpoch_hAnc, witEpoch_hLink, witEpoch_hAcc, witEpoch_hDev⟩

theorem witness_corduroy_real_params :
    ∃ params : PqHashParams,
      (params.w = 4 ∨ params.w = 16) ∧ params.statefulJorts = false :=
  ⟨corduroyPoseidon2AggParams, .inl rfl, rfl⟩

attribute [local irreducible]
  cshakeFrontierHashSuite prehashFaultSuite
  deriveFrontierPk signFrontierFts verifyFrontierFts verifyRotatedEpochChain
  witCompact1122H witCompact1122Sig witEpochM1 witEpochM2 witEpochH witEpochPk witEpochSig

set_option maxRecDepth 32768

#tooth_pair Qsag.compact1122_one_time_euf_cma_reduction vs Qsag.tooth_drop_target_sum_allows_one_sig_forgery

#tooth_pair Qsag.rotatedEpochVote_forward_secure_chain vs Qsag.tooth_static_key_compromise_forges_historical_epoch

#tooth_pair Qsag.corduroy_threshold_stateless_euf_cma vs Qsag.tooth_corduroy_t_corrupted_custodians_uniquely_pin_secret

#verify_inhabited Qsag.compact1122_one_time_euf_cma_reduction Qsag.witness_compact1122_forgery

#verify_inhabited Qsag.rotatedEpochVote_forward_secure_chain Qsag.witness_rotatedEpochVote_chain

#verify_inhabited Qsag.corduroy_threshold_stateless_euf_cma Qsag.witness_corduroy_real_params

#verify_constructive Qsag.tooth_drop_target_sum_allows_one_sig_forgery Qsag.tooth_static_key_compromise_forges_historical_epoch

end Qsag

end
end

/-! ## `Qsag.Protocol.Signing.ProdCollision` -/
public section
public section

namespace Qsag

set_option autoImplicit false

-- Hypertree position of the path at layer `i`.
set_option hygiene false in
local notation:max "pos⟪" i "⟫" => sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)

-- Tree address of the path at layer `i`.
set_option hygiene false in
local notation:max "tree⟪" i "⟫" =>
  UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight)

-- Key-pair (leaf) index of the path at layer `i`.
set_option hygiene false in
local notation:max "kp⟪" i "⟫" =>
  (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)

-- Layer-`i` XMSS signature of the forgery.
set_option hygiene false in
local notation:max "lsig⟪" i "⟫" => (sigStar.layerSigs.getD i ⟨0, [], []⟩)

-- Honest public root.
set_option hygiene false in
local notation:max "PK_ROOT" => (derivePublicKey suite params sk).pkRoot

-- Root of the top subtree, as the verifier walk reaches it.
set_option hygiene false in
local notation:max "TOP_ROOT" =>
  (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
    (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight))))

-- FORS tree address, key pair and leaf indices of the forgery.
set_option hygiene false in
local notation:max "FORS_TREE" => (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))

set_option hygiene false in
local notation:max "FORS_KP" => (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)

set_option hygiene false in
local notation:max "FORS_IDXS" =>
  (prodSigForsIdxs suite params (derivePublicKey suite params sk) msgStar sigStar)

/-- On the concrete accepted toy forgery the extractor output is inhabited. -/
theorem production_forgery_witness_inhabited :
    Nonempty (ProdTcrWitness crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] []
      prodToyForgery) ∨
    ProdPreimageBreak crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] [] prodToyForgery :=
  production_stateful_forgery_witness crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] []
    prodToyForgery (.inl rfl) rfl (fun _ h => by cases h) (fun _ h => by cases h)
    prodToyForgery_accepted

end Qsag

end

public section

namespace Qsag

set_option autoImplicit false

theorem prodToyRadix : prodToyStatefulParams.w = 4 ∨ prodToyStatefulParams.w = 16 := .inl rfl

theorem prodToyOneTime : prodToyStatefulParams.statefulJorts = true →
    ∀ q, q ∈ ([] : List ProdSigningQuery) → ∀ q', q' ∈ ([] : List ProdSigningQuery) →
      q.epoch = q'.epoch → q = q' :=
  fun _ _ h => by cases h

/-- **The reduction returns a collision on a concrete accepted forgery.** On the accepted toy
    forgery (`prodToyForgery_accepted`, constant hash, empty log) the extractor evaluates, in the
    kernel, to a returned `(target, colliding input)` pair. -/
theorem prodToyForgery_returns_collision :
    (prodTcrOutput crumbToySuite prodToyStatefulParams prodToyRadix
      ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime).isSome = true := by
  decide +kernel

/-- Hence a checked on-path collision exists for that forgery, obtained from the extractor. -/
theorem prodToyForgery_checked_collision :
    ∃ t forged,
      t.OnPath prodToyStatefulParams [] prodToyForgery.leafGlobalIdx
        (prodSigForsIdxs crumbToySuite prodToyStatefulParams
          (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩) [] prodToyForgery) ∧
      prodTcrCheck crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ prodToyForgery.leafGlobalIdx
        t forged = true := by
  cases hOut : prodTcrOutput crumbToySuite prodToyStatefulParams prodToyRadix
      ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime with
  | none =>
    have h := prodToyForgery_returns_collision
    rw [hOut] at h
    cases h
  | some p =>
    obtain ⟨_, hOn, _, hChk⟩ := prodTcrOutput_sound crumbToySuite prodToyStatefulParams prodToyRadix
      ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime p.1 p.2 hOut
    exact ⟨p.1, p.2, hOn, hChk⟩

end Qsag

end

#verify_constructive Qsag.prodToyForgery_returns_collision Qsag.prodToyForgery_checked_collision
end

/-! ## `Qsag.Protocol.Signing.SignatureOutputAndCacheLaws` -/
public section
public section

namespace Qsag

-- Literal encoding certificates avoid any UTF-8 decoding or choice principle.
private theorem signaturePrfMsgBytes :
    "QSAG.PQ.PRFMSG/v1".toByteArray.data.toList = [81, 83, 65, 71, 46, 80, 81, 46, 80, 82, 70, 77, 83, 71, 47, 118, 49] := by rfl

private theorem signatureHMsgBytes :
    "QSAG.PQ.HMSG/v1".toByteArray.data.toList = [81, 83, 65, 71, 46, 80, 81, 46, 72, 77, 83, 71, 47, 118, 49] := by rfl

private theorem signaturePrfBytes :
    "QSAG.PQ.PRF/v1".toByteArray.data.toList = [81, 83, 65, 71, 46, 80, 81, 46, 80, 82, 70, 47, 118, 49] := by rfl

private theorem signatureThFBytes :
    "QSAG.PQ.TH_F/v1".toByteArray.data.toList = [81, 83, 65, 71, 46, 80, 81, 46, 84, 72, 95, 70, 47, 118, 49] := by rfl

private theorem signatureThHBytes :
    "QSAG.PQ.TH_H/v1".toByteArray.data.toList = [81, 83, 65, 71, 46, 80, 81, 46, 84, 72, 95, 72, 47, 118, 49] := by rfl

private theorem signatureThTlBytes :
    "QSAG.PQ.TH_TL/v1".toByteArray.data.toList = [81, 83, 65, 71, 46, 80, 81, 46, 84, 72, 95, 84, 76, 47, 118, 49] := by rfl

private theorem signatureHPreBytes :
    "QSAG.PQ.PRE/v1".toByteArray.data.toList = [81, 83, 65, 71, 46, 80, 81, 46, 80, 82, 69, 47, 118, 49] := by rfl

attribute [local simp] signaturePrfMsgBytes signatureHMsgBytes signaturePrfBytes
  signatureThFBytes signatureThHBytes signatureThTlBytes signatureHPreBytes

/-! ### Non-First-Hit Bias `#tooth` Theorem over Real `verifyPqHashSig` (`w=4, ell1=128, target=192`) -/

/-- Canonical 1-layer WOTS+C parameter set at deployed `(w = 4, ell1 = 128, targetSum = 192)`. -/
def wotsSingleLayerParams : PqHashParams := ⟨4, 128, 1, 1, 0, 0, 1, true⟩

/-- Construct a 1-layer `PqHashSig` at an explicitly chosen counter `chosenCtr` when `checkTargetSum` holds. -/
def evalSingleLayerAtCounter (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg rRand : List UInt8) (chosenCtr : Nat) : Option PqHashSig :=
  if !(params.wellFormed) || !(params.statefulJorts) || params.numLayers ≠ 1 then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let hmsg := thHashMsg suite rRand pk.pkSeed pk.pkRoot mu 0 0 0 chosenCtr
    let digits := extractBaseWDigits params.w params.ell1 hmsg
    if !(checkTargetSum params.w params.ell1 params.targetSum digits) then none
    else
      let wotsChains := (List.range params.ell1).map fun r =>
        wotsChainSteps suite sk.pkSeed 0 0 0 r 0 (digits.getD r 0) (wotsSecretBase suite sk 0 0 0 r)
      let authPath := buildMerkleAuthPath suite sk.pkSeed 0 0 .tree
        (computeWotsPk suite params sk 0 0) params.subtreeHeight 0 0
      some { rRand := rRand, msgTswCtr := 0, leafGlobalIdx := 0, forsOpenings := [],
             layerSigs := [{ tswCtr := chosenCtr, wotsChains := wotsChains, authPath := authPath }] }

/-- **Symbolic Verification of Any Valid Counter (`verifyPqHashSig_evalSingleLayerAtCounter`)**:
    ANY counter `chosenCtr` satisfying `checkTargetSum` produces a signature accepted by `verifyPqHashSig`! -/
theorem verifyPqHashSig_evalSingleLayerAtCounter
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg rRand : List UInt8) (chosenCtr : Nat) (sig : PqHashSig)
    (hEval : evalSingleLayerAtCounter suite params sk msg rRand chosenCtr = some sig) :
    verifyPqHashSig suite params (derivePublicKey suite params sk) msg sig = true := by
  unfold evalSingleLayerAtCounter at hEval
  cases hWf : params.wellFormed
  · simp [hWf] at hEval
  · cases hSt : params.statefulJorts
    · simp [hWf, hSt] at hEval
    · cases hL1 : decide (params.numLayers = 1)
      · have hNe1 : params.numLayers ≠ 1 := of_decide_eq_false hL1
        simp [hWf, hSt, hNe1] at hEval
      · have hEq1 : params.numLayers = 1 := of_decide_eq_true hL1
        simp only [hWf, hSt, hEq1, ne_eq, not_true_eq_false, Bool.not_true, Bool.or_self, decide_false] at hEval
        let pk := derivePublicKey suite params sk
        let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
        let hmsg := thHashMsg suite rRand pk.pkSeed pk.pkRoot mu 0 0 0 chosenCtr
        let digits := extractBaseWDigits params.w params.ell1 hmsg
        cases hChk : checkTargetSum params.w params.ell1 params.targetSum digits
        · rw [show checkTargetSum params.w params.ell1 params.targetSum digits = false from hChk] at hEval
          simp at hEval
        · rw [show checkTargetSum params.w params.ell1 params.targetSum digits = true from hChk] at hEval
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hEval
          subst hEval
          have hZeroLt : 0 < 2 ^ (params.numLayers * params.subtreeHeight) := Nat.two_pow_pos _
          unfold verifyPqHashSig
          simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_singleton,
            hEq1, ne_eq, not_true_eq_false, Nat.two_pow_pos, decide_false, Bool.or_false, decide_true, hSt, List.isEmpty_nil]
          simp only [verifyHypertreeLayers_nil, verifyHypertreeLayers_cons, Nat.zero_mod, Nat.zero_div]
          change (let hm := hmsg; _) = true
          dsimp only
          have hChainsLen : ((List.range params.ell1).map fun r =>
              wotsChainSteps suite sk.pkSeed 0 0 0 r 0 (digits.getD r 0)
                (wotsSecretBase suite sk 0 0 0 r)).length = params.ell1 := by simp
          dsimp only [digits, hmsg, mu, pk] at hChk
          simp only [show UInt32.ofNat 0 = (0 : UInt32) from rfl,
            show UInt64.ofNat 0 = (0 : UInt64) from rfl]
          rw [hChk]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_map, List.length_range, ne_eq, not_true_eq_false]
          have hWots := recoverWotsPkFromSig_eq_computeWotsPk suite params sk 0 0 0 digits hChk
          dsimp only at hWots
          dsimp only [digits, hmsg, mu, pk] at hWots
          simp only [derivePublicKey] at hWots ⊢
          rw [hWots]
          have hWalk := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed 0 0 .tree
            (computeWotsPk suite params sk 0 0) params.subtreeHeight 0 0 (Nat.two_pow_pos _)
          simp only [Nat.zero_mul, Nat.zero_add] at hWalk
          rw [hWalk]
          simp only [hEq1, Nat.sub_self]
          simp only [computeXmssSubtreeRoot, show UInt32.ofNat 0 = (0 : UInt32) from rfl, decide_true]

/-- Domain-sensitive 32-byte `TweakableHashSuite` exhibiting LSB steering when non-first-hit counters are allowed. -/
def lsbBiasRawHash (pre : List UInt8) : List UInt8 :=
  if pre.getD 1 0 == 14 then
    -- `tagPrf` (`wotsSecretBase`): chain base byte 0 is `0x00` (`lsb = false`)
    0x00 :: List.replicate 31 0x1B
  else if pre.getD 10 0 == 72 && pre.getLastD 0 == 0 && !(pre.contains 0xFE) then
    -- `tagHMsg` on coin `0` (`rRand = [0x00]`) at `ctr = 0`: byte 0 is `0x1B` (`digits[0] = 0`, sum = 192)
    0x1B :: List.replicate 31 0x1B
  else
    -- `tagHMsg` at `ctr = 1` or coin `1` (`rRand = [0xFE]`): byte 0 is `0x4B` (`digits[0] = 1`, sum = 192),
    -- and `tagThF` outputs byte 0 = `0x1B` (`lsb = true`)!
    0x4B :: List.replicate 31 0x1B

def lsbBiasSuite : TweakableHashSuite where
  suiteId := [0x01]
  rawHash := lsbBiasRawHash
  rawHash_len := fun pre => by
    unfold lsbBiasRawHash
    split <;> (try split) <;> (try split) <;> simp

private theorem signatureFirstDigit (bytes : List UInt8) :
    (extractBaseWDigits 4 128 bytes)[0]? = some ((bytes.getD 0 0).toNat / 64 % 4) := by
  simp [extractBaseWDigits_eq]

private theorem signatureOddByte : ((0x4B : UInt8) &&& 1) = 1 := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_and]
  decide

private theorem lsbBiasSuiteNodeH (seed x y : List UInt8) (adrs : HashAdrs) :
    thNodeH lsbBiasSuite seed adrs x y = 0x4B :: List.replicate 31 0x1B := by
  simp [thNodeH, thCall_eq, thPreimage_eq, lsbBiasSuite, lsbBiasRawHash,
    encodeMultiFrame, encodeByteFields, encodeListField, tagThH, byteArray_toList_eq,
    leb128, leb128Aux]

private theorem lsbBiasSuitePublicKey (sk : PqSecretKey) :
    derivePublicKey lsbBiasSuite wotsSingleLayerParams sk =
      ⟨sk.pkSeed, 0x4B :: List.replicate 31 0x1B⟩ := by
  simp only [derivePublicKey, computeXmssSubtreeRoot, wotsSingleLayerParams, computeMerkleNode]
  rw [lsbBiasSuiteNodeH]

def reuseDigest1 : List UInt8 := 0x0F :: List.replicate 31 0x1B
def reuseDigest2 : List UInt8 := 0xF0 :: List.replicate 31 0x1B
def reuseDigest3 : List UInt8 := 0x5A :: List.replicate 31 0x1B

def bottomReuseRawHash (pre : List UInt8) : List UInt8 :=
  if pre.getD 10 0 == 80 && pre.getD 11 0 == 82 && pre.getD 12 0 == 69 then
    -- `tagHPre` (`"QSAG.PQ.PRE/v1"`): preserve last message byte in byte 0
    pre.getLastD 0 :: List.replicate 31 0x1B
  else if pre.getD 10 0 == 72 then
    -- `tagHMsg`: map `mu[0] ∈ {1, 2, 3}` to `reuseDigest1`, `reuseDigest2`, `reuseDigest3`
    if pre.contains 0xE1 then reuseDigest1
    else if pre.contains 0xE2 then reuseDigest2
    else reuseDigest3
  else
    0x1B :: List.replicate 31 0x1B

def bottomReuseSuite : TweakableHashSuite where
  suiteId := [0x02]
  rawHash := bottomReuseRawHash
  rawHash_len := fun pre => by
    unfold bottomReuseRawHash reuseDigest1 reuseDigest2 reuseDigest3
    split
    · simp
    · split <;> (try split) <;> (try split) <;> simp

private theorem bottomReuseSuiteNodeH (seed x y : List UInt8) (adrs : HashAdrs) :
    thNodeH bottomReuseSuite seed adrs x y = 0x1B :: List.replicate 31 0x1B := by
  simp [thNodeH, thCall_eq, thPreimage_eq, bottomReuseSuite, bottomReuseRawHash,
    encodeMultiFrame, encodeByteFields, encodeListField, tagThH, byteArray_toList_eq,
    leb128, leb128Aux]

private theorem bottomReuseSuitePublicKey (sk : PqSecretKey) :
    derivePublicKey bottomReuseSuite wotsSingleLayerParams sk =
      ⟨sk.pkSeed, 0x1B :: List.replicate 31 0x1B⟩ := by
  simp only [derivePublicKey, computeXmssSubtreeRoot, wotsSingleLayerParams, computeMerkleNode]
  rw [bottomReuseSuiteNodeH]

set_option autoImplicit false

set_option maxRecDepth 8192

set_option maxHeartbeats 1000000

attribute [local instance] signatureUInt8LawfulBEq

attribute [local instance] signatureUInt8LawfulEqOrd

attribute [local instance] signatureUInt8LawfulOrderOrd

attribute [local simp] signaturePrfMsgBytes signatureHMsgBytes signaturePrfBytes
  signatureThFBytes signatureThHBytes signatureThTlBytes signatureHPreBytes

/-- Extract the least-significant bit of the first WOTS+C chain byte of a `PqHashSig`. -/
def sigChainLsb (sig : PqHashSig) : Bool :=
  (((sig.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains.getD 0 []).getD 0 0 &&& 1) == 1

private theorem signatureToyDigestValid (b : UInt8)
    (hb : b = 0x1B ∨ b = 0x4B ∨ b = 0x0F ∨ b = 0xF0 ∨ b = 0x5A) :
    checkTargetSum 4 128 192 (extractBaseWDigits 4 128
      ((b :: List.replicate 31 0x1B) ++ (b :: List.replicate 31 0x1B))) = true := by
  rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    simp [extractBaseWDigits, checkTargetSum, sumDigits, List.range_succ] <;> decide

private theorem signatureToyDigestValidExpanded (b : UInt8)
    (hb : b = 0x1B ∨ b = 0x4B ∨ b = 0x0F ∨ b = 0xF0 ∨ b = 0x5A) :
    checkTargetSum 4 128 192 (extractBaseWDigits 4 128
      [b, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B,
       b, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B, 0x1B]) = true := by
  simpa only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
    using signatureToyDigestValid b hb

def coinTwoRand (c : Fin 2) : List UInt8 :=
  if c.val == 0 then [0x00] else [0xFE]

def honestReferenceLsbSampler (c : Fin 2) : Option PqHashSig :=
  let pk := derivePublicKey lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩
  let mu := thPreHash lsbBiasSuite pk.pkSeed pk.pkRoot []
  let rRand := coinTwoRand c
  match firstValidCounter (fun ctr =>
      checkTargetSum 4 128 192 (extractBaseWDigits 4 128
        (thHashMsg lsbBiasSuite rRand pk.pkSeed pk.pkRoot mu 0 0 0 ctr))) 4 with
  | none => none
  | some ctr0 => evalSingleLayerAtCounter lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩ [] rRand ctr0

/-- Malicious coordinator: inspects valid first-hit `ctr₀`; whenever `sigChainLsb sig₀ = false`, skips
    `ctr₀` and selects `ctr₁ = ctr₀ + 1` instead! -/
def maliciousSkipLsbZeroSampler (c : Fin 2) : Option PqHashSig :=
  let pk := derivePublicKey lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩
  let mu := thPreHash lsbBiasSuite pk.pkSeed pk.pkRoot []
  let rRand := coinTwoRand c
  match firstValidCounter (fun ctr =>
      checkTargetSum 4 128 192 (extractBaseWDigits 4 128
        (thHashMsg lsbBiasSuite rRand pk.pkSeed pk.pkRoot mu 0 0 0 ctr))) 4 with
  | none => none
  | some ctr0 =>
    match evalSingleLayerAtCounter lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩ [] rRand ctr0 with
    | none => none
    | some sig0 =>
      if sigChainLsb sig0 then some sig0
      else evalSingleLayerAtCounter lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩ [] rRand (ctr0 + 1)

/-- **`#tooth` Non-First-Hit Coordinator Bias Theorem (`tooth_non_first_hit_lsb_bias_positive_tvd`)**:
    Skipping valid first-hit counter `ctr₀ = 0` when `sigChainLsb = false` in favor of `ctr₁ = 1 > ctr₀`
    produces signatures that **100% pass `verifyPqHashSig = true` on EVERY coin**, yet induces
    strictly positive statistical distance (`statisticalDistance = 2 > 0`, `TVD = 1/2 > 0`) from the
    honest `firstValidCounter` reference signer! -/
theorem tooth_non_first_hit_lsb_bias_positive_tvd :
    ∃ (pk : PqPublicKey),
      pk = derivePublicKey lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩ ∧
      (∀ c : Fin 2, ∃ sig,
        maliciousSkipLsbZeroSampler c = some sig ∧
        verifyPqHashSig lsbBiasSuite wotsSingleLayerParams pk [] sig = true) ∧
      statisticalDistance 2 [false, true]
        (fun c => (honestReferenceLsbSampler c).elim false sigChainLsb)
        (fun c => (maliciousSkipLsbZeroSampler c).elim false sigChainLsb) = 2 ∧
      0 < statisticalDistance 2 [false, true]
        (fun c => (honestReferenceLsbSampler c).elim false sigChainLsb)
        (fun c => (maliciousSkipLsbZeroSampler c).elim false sigChainLsb) := by
  refine ⟨derivePublicKey lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩, rfl, ?_, ?_, ?_⟩
  · intro c
    refine ⟨(maliciousSkipLsbZeroSampler c).getD ⟨[], 0, 0, [], []⟩, ?_⟩
    have h : ∀ c : Fin 2,
        maliciousSkipLsbZeroSampler c = some ((maliciousSkipLsbZeroSampler c).getD ⟨[], 0, 0, [], []⟩) ∧
        verifyPqHashSig lsbBiasSuite wotsSingleLayerParams
          (derivePublicKey lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩) []
          ((maliciousSkipLsbZeroSampler c).getD ⟨[], 0, 0, [], []⟩) = true := by
      simp only [maliciousSkipLsbZeroSampler, coinTwoRand,
        evalSingleLayerAtCounter, ↓lsbBiasSuitePublicKey,
        firstValidCounter, firstValidCounterAux, sigChainLsb]

      simp [wotsSingleLayerParams, thHashMsg, thPreHash, thCall, thPreimage, encodeMultiFrame, encodeByteFields,
        encodeListField, leb128, leb128Aux, be, byteArray_toList_eq,
        computeMerkleNode,
        computeWotsPk, computeWotsEndpoints, wotsChainSteps, wotsSecretBase, thSecretPrf,
        thTweakTl, thNodeH, thChainF, PqHashParams.wellFormed, PqHashParams.targetSum,
        canonicalTargetSum, signatureToyDigestValidExpanded, signatureFirstDigit, signatureOddByte,
        verifyPqHashSig, verifyHypertreeLayers, recoverWotsPkFromSig, recoverWotsEndpoints,
        walkMerkleAuthPath, buildMerkleAuthPath, encodeAdrs, AdrsKind.toCode,
        tagPrf, tagThF, tagThH, tagThTl, tagHMsg, tagHPre, zeroAdrs, lsbBiasSuite, lsbBiasRawHash] <;> decide
    exact h c
  · simp only [statisticalDistance, coinMass, natAbsDiff, qsum, maliciousSkipLsbZeroSampler,
      honestReferenceLsbSampler, coinTwoRand, evalSingleLayerAtCounter, ↓lsbBiasSuitePublicKey,
      firstValidCounter, firstValidCounterAux, sigChainLsb]

    simp [wotsSingleLayerParams, thHashMsg, thPreHash, thCall, thPreimage, encodeMultiFrame, encodeByteFields,
        encodeListField, leb128, leb128Aux, be, byteArray_toList_eq,
        computeMerkleNode,
        computeWotsPk, computeWotsEndpoints, wotsChainSteps, wotsSecretBase, thSecretPrf,
        thTweakTl, thChainF, PqHashParams.wellFormed, PqHashParams.targetSum,
        canonicalTargetSum, signatureToyDigestValidExpanded, signatureFirstDigit, sigChainLsb, signatureOddByte,
        buildMerkleAuthPath, encodeAdrs, AdrsKind.toCode,
        tagPrf, tagThF, tagThTl, tagHMsg, tagHPre, zeroAdrs, lsbBiasSuite, lsbBiasRawHash] <;> decide
  · simp only [statisticalDistance, coinMass, natAbsDiff, qsum, maliciousSkipLsbZeroSampler,
      honestReferenceLsbSampler, coinTwoRand, evalSingleLayerAtCounter, ↓lsbBiasSuitePublicKey,
      firstValidCounter, firstValidCounterAux, sigChainLsb]

    simp [wotsSingleLayerParams, thHashMsg, thPreHash, thCall, thPreimage, encodeMultiFrame, encodeByteFields,
        encodeListField, leb128, leb128Aux, be, byteArray_toList_eq,
        computeMerkleNode,
        computeWotsPk, computeWotsEndpoints, wotsChainSteps, wotsSecretBase, thSecretPrf,
        thTweakTl, thChainF, PqHashParams.wellFormed, PqHashParams.targetSum,
        canonicalTargetSum, signatureToyDigestValidExpanded, signatureFirstDigit, sigChainLsb, signatureOddByte,
        buildMerkleAuthPath, encodeAdrs, AdrsKind.toCode,
        tagPrf, tagThF, tagThTl, tagHMsg, tagHPre, zeroAdrs, lsbBiasSuite, lsbBiasRawHash] <;> decide

/-- Exhausted counter budget `#tooth` refutation (`tooth_exhausted_grinder_aborts_none`). -/
theorem tooth_exhausted_grinder_aborts_none :
    ∃ (check : Nat → Bool) (maxTrials : Nat),
      check = (fun ctr => decide (ctr = 5)) ∧ maxTrials = 5 ∧
      check 5 = true ∧ firstValidCounter check maxTrials = none :=
  ⟨fun ctr => decide (ctr = 5), 5, rfl, rfl, by decide, by decide⟩

/-- **`#tooth` Bottom-Layer Leaf-Reuse WOTS+C Forgery (`tooth_caching_bottom_layer_breaks_wots_one_time`)**:
    Concrete weak-suite counterexample to allowing bottom-layer (`layer = 0`) WOTS+C leaf reuse:
    two distinct messages `m₁ = [0xE1] ≠ [0xE2] = m₂` exposes two `TSW`-valid (`w = 4, ell1 = 128,
    targetSum = 192`) chain vectors `sig₁, sig₂` from which the public chain-splicing
    function `forgeWotsFromTwoSigs` constructs a **valid `PqHashSig` accepted by `verifyPqHashSig`
    (`= true`) on an unqueried third message `m₃ = [0xE3] ∉ [m₁, m₂]`**! -/
theorem tooth_caching_bottom_layer_breaks_wots_one_time :
    ∃ (m₁ m₂ m₃ : List UInt8) (pk : PqPublicKey) (sig₁ sig₂ forgedSig₃ : PqHashSig),
      m₁ = [0xE1] ∧ m₂ = [0xE2] ∧ m₃ = [0xE3] ∧
      m₁ ≠ m₂ ∧ m₃ ∉ [m₁, m₂] ∧
      pk = derivePublicKey bottomReuseSuite wotsSingleLayerParams ⟨[], [], []⟩ ∧
      evalSingleLayerAtCounter bottomReuseSuite wotsSingleLayerParams ⟨[], [], []⟩ m₁ [] 0 = some sig₁ ∧
      evalSingleLayerAtCounter bottomReuseSuite wotsSingleLayerParams ⟨[], [], []⟩ m₂ [] 0 = some sig₂ ∧
      verifyPqHashSig bottomReuseSuite wotsSingleLayerParams pk m₁ sig₁ = true ∧
      verifyPqHashSig bottomReuseSuite wotsSingleLayerParams pk m₂ sig₂ = true ∧
      verifyPqHashSig bottomReuseSuite wotsSingleLayerParams pk m₃ forgedSig₃ = true := by
  let sk : PqSecretKey := ⟨[], [], []⟩
  let pk := derivePublicKey bottomReuseSuite wotsSingleLayerParams sk
  let sig1 := (evalSingleLayerAtCounter bottomReuseSuite wotsSingleLayerParams sk [0xE1] [] 0).getD
    ⟨[], 0, 0, [], []⟩
  let sig2 := (evalSingleLayerAtCounter bottomReuseSuite wotsSingleLayerParams sk [0xE2] [] 0).getD
    ⟨[], 0, 0, [], []⟩
  let chains := forgeWotsFromTwoSigs bottomReuseSuite pk.pkSeed 0 0 0 128
    (extractBaseWDigits 4 128 reuseDigest1) (extractBaseWDigits 4 128 reuseDigest2)
    (extractBaseWDigits 4 128 reuseDigest3)
    (sig1.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains
    (sig2.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains
  let forged : PqHashSig := { sig1 with layerSigs :=
    [{ sig1.layerSigs.getD 0 ⟨0, [], []⟩ with wotsChains := chains }] }
  refine ⟨[0xE1], [0xE2], [0xE3], pk, sig1, sig2, forged,
    rfl, rfl, rfl, by decide, by decide, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [forged, chains, sig1, sig2, pk, sk, evalSingleLayerAtCounter, ↓bottomReuseSuitePublicKey,
      reuseDigest1, reuseDigest2, reuseDigest3, forgeWotsFromTwoSigs] <;>

    simp [wotsSingleLayerParams, thHashMsg, thPreHash, thCall, thPreimage, encodeMultiFrame, encodeByteFields,
        encodeListField, leb128, leb128Aux, be, byteArray_toList_eq,
        computeMerkleNode,
        computeWotsPk, computeWotsEndpoints, wotsChainSteps, wotsSecretBase, thSecretPrf,
        thTweakTl, thNodeH, thChainF, PqHashParams.wellFormed, PqHashParams.targetSum,
        canonicalTargetSum, signatureToyDigestValidExpanded,
        verifyPqHashSig, verifyHypertreeLayers, recoverWotsPkFromSig, recoverWotsEndpoints,
        walkMerkleAuthPath, buildMerkleAuthPath, encodeAdrs, AdrsKind.toCode,
        tagPrf, tagThF, tagThH, tagThTl, tagHMsg, tagHPre, zeroAdrs,
        bottomReuseSuite, bottomReuseRawHash, reuseDigest1, reuseDigest2, reuseDigest3] <;> decide

#verify_constructive tooth_non_first_hit_lsb_bias_positive_tvd

#verify_constructive tooth_exhausted_grinder_aborts_none

#verify_constructive tooth_caching_bottom_layer_breaks_wots_one_time

end Qsag

end
end

/-! ## `Qsag.Protocol.Signing.ProdHashReductions` -/
public section
public section

namespace Qsag

set_option autoImplicit false

/-- Replaying a message obtained from a signing query loses `eufCmaWithinWin`. -/
theorem tooth_replayed_query_loses_eufCmaWithin (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (q : ProdSigningQuery) (sig : PqHashSig)
    (hSign : prodSignQuery suite params sk q = some sig) :
    eufCmaWithinWin suite params sk
      (fun _ => .querySign q (fun resp => .done (q.message, resp.getD sig))) = false := by
  unfold eufCmaWithinWin runHashSignAdv challengerSignStep
  have hNoConf : challengerEpochConflict params [] q = false := by
    simp [challengerEpochConflict]
  rw [hNoConf]
  dsimp only [Bool.false_eq_true, ↓reduceIte, runHashSignAdv]
  apply prodEufCmaWin_rejects_signed_message suite params _ sig
  simp [productionSigningLog, hSign]

/-- `#tooth`: Submitting the target preimage itself (`forged = target.input`) is rejected by
    `smDtTcrChallengerCheck`, even though its hash collides trivially. -/
theorem tooth_identical_input_rejected_by_smDtTcr (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (qs : List ProdSigningQuery)
    (leaf : Nat) (idxs : List Nat) (t : ProdTargetIdx) :
    smDtTcrChallengerCheck suite params sk qs
      (some ⟨leaf, idxs, t, t.input suite params sk leaf⟩) = false := by
  simp [smDtTcrChallengerCheck, prodTcrCheck]

/-- All-zero 32-byte suite: base-4 digit sum is `0 ≠ 192`, so `prodToyForgery` is rejected at layer 0. -/
def zeroRejectToySuite : TweakableHashSuite where
  suiteId := []
  rawHash := fun _ => List.replicate 32 0x00
  rawHash_len := fun _ => List.length_replicate

theorem prodToyForgery_rejected_by_zeroSuite :
    verifyProductionPqHashSig zeroRejectToySuite prodToyStatefulParams
      (derivePublicKey zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩)
      [] prodToyForgery = false := by
  decide +kernel

theorem prodToyForgery_zeroSuite_cands_nil :
    (publicVerifierWithTcrCands zeroRejectToySuite prodToyStatefulParams
      (derivePublicKey zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩)
      [] [] prodToyForgery).2 = [] := by
  decide +kernel

def prodToyForgerAdv : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig) :=
  fun _ => .done ([], prodToyForgery)

theorem prodToyForgerAdv_within (pk : PqPublicKey) : (prodToyForgerAdv pk).Within 0 0 := trivial

def prodToyAcceptCoin : ProdExperimentCoin :=
  ⟨crumbToySuite, crumbToySuite, crumbToySuite, ⟨[], [], []⟩⟩

def prodToyRejectCoin : ProdExperimentCoin :=
  ⟨zeroRejectToySuite, zeroRejectToySuite, zeroRejectToySuite, ⟨[], [], []⟩⟩

/-- Concrete 8-coin ensemble (`3` accepting coins + `5` rejecting coins). -/
def prodToyGameCoins : List ProdExperimentCoin :=
  [prodToyAcceptCoin, prodToyAcceptCoin, prodToyAcceptCoin,
   prodToyRejectCoin, prodToyRejectCoin, prodToyRejectCoin, prodToyRejectCoin, prodToyRejectCoin]

/-- **Two-Sided Nonvacuity (`0 < wins ∧ wins < totalCoins`):**
    On `prodToyGameCoins` (`totalCoins = 8`), `eufCmaRealWithinWins = 3` (`0 < 3 < 8`) and the
    constructed seed-withheld reduction `bestTcrExtractorAdv` achieves `0 < smDtTcrWithinWins` and
    `smDtTcrWithinWins < 8`. -/
theorem prodToyGameCoins_two_sided_nonvacuous :
    0 < eufCmaRealWithinWins prodToyGameCoins prodToyStatefulParams prodToyForgerAdv ∧
    eufCmaRealWithinWins prodToyGameCoins prodToyStatefulParams prodToyForgerAdv <
      prodToyGameCoins.length ∧
    0 < smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams
      (bestTcrExtractorAdv prodToyGameCoins prodToyStatefulParams 0 prodToyForgerAdv) ∧
    smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams
      (bestTcrExtractorAdv prodToyGameCoins prodToyStatefulParams 0 prodToyForgerAdv) <
      prodToyGameCoins.length := by
  have hAccWin : eufCmaWithinWin crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
      prodToyForgerAdv = true := by
    unfold eufCmaWithinWin prodToyForgerAdv runHashSignAdv prodEufCmaWin productionSigningLog
    dsimp only
    rw [prodToyForgery_accepted]
    rfl
  have hRejLose : eufCmaWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩
      prodToyForgerAdv = false := by
    unfold eufCmaWithinWin prodToyForgerAdv runHashSignAdv prodEufCmaWin
    dsimp only
    rw [prodToyForgery_rejected_by_zeroSuite]
    rfl
  have hRealCount :
      eufCmaRealWithinWins prodToyGameCoins prodToyStatefulParams prodToyForgerAdv = 3 := by
    simp [eufCmaRealWithinWins, prodToyGameCoins, prodToyAcceptCoin, prodToyRejectCoin,
      hitCount, hAccWin, hRejLose]
  let B_tcr := bestTcrExtractorAdv prodToyGameCoins prodToyStatefulParams 0 prodToyForgerAdv
  have hToyTcrEv :
      (let r := runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
        (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩))
      prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix ⟨⟨[], [], []⟩, r.2, r.1.1, r.1.2⟩
        (runHashSignAdv_queries_oneTime crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)))) =
        true := by
    have hEqEv :
        (let r := runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩))
        prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix ⟨⟨[], [], []⟩, r.2, r.1.1, r.1.2⟩
          (runHashSignAdv_queries_oneTime crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
            (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)))) =
        prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix
          ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime := rfl
    rw [hEqEv]
    unfold prodTcrEvent
    cases hOut : prodTcrOutput crumbToySuite prodToyStatefulParams prodToyRadix
        ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime with
    | none =>
      have hc := prodToyForgery_returns_collision
      rw [hOut] at hc; cases hc
    | some p =>
      exact (prodTcrOutput_sound crumbToySuite prodToyStatefulParams prodToyRadix
        ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime p.1 p.2 hOut).2.2.2
  have hTcrPos : 0 < smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams B_tcr := by
    obtain ⟨slot, hSlotWin⟩ := prodTcrEvent_captured_by_slot crumbToySuite prodToyStatefulParams
      prodToyRadix (qh := 0) (qs_max := 0) ⟨[], [], []⟩ prodToyForgerAdv prodToyForgerAdv_within
      hToyTcrEv
    have hSlotGe1 : 1 ≤ smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams
        (tcrExtractorAdv prodToyStatefulParams slot.val prodToyForgerAdv) := by
      unfold smDtTcrWithinWins prodToyGameCoins prodToyAcceptCoin hitCount
      dsimp only
      simp only [hSlotWin, ↓reduceIte]
      omega
    have hBestGe := bestFinIdx_ge (prodPathTargetCount prodToyStatefulParams 0)
      (by unfold prodPathTargetCount; omega)
      (fun k => smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams
        (tcrExtractorAdv prodToyStatefulParams k.val prodToyForgerAdv)) slot
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hSlotGe1 hBestGe)
  have hRejTcrFalse : ∀ slot : Nat,
      smDtTcrWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩
        (tcrExtractorAdv prodToyStatefulParams slot prodToyForgerAdv) = false := by
    intro slot
    unfold smDtTcrWithinWin tcrExtractorAdv advCollectTcrSubmissions HashSignAdv.map
    rw [runHashSignAdv_bind, runHashSignAdv_advTrackSignLog zeroRejectToySuite
      prodToyStatefulParams ⟨[], [], []⟩ [] [] _ rfl]
    dsimp only [prodToyForgerAdv, runHashSignAdv, productionSigningLog]
    rw [runHashSignAdv_bind]
    dsimp only [HashSignAdv.bind]
    rw [runHashSignAdv_bind]
    dsimp only [advRawHash, runHashSignAdv]
    rw [runHashSignAdv_bind, runHashSignAdv_advDeriveProductionStatelessInputs]
    dsimp only
    rw [runHashSignAdv_bind, runHashSignAdv_advVerifyWithTcrCands]
    dsimp only [runHashSignAdv]
    rw [prodToyForgery_zeroSuite_cands_nil]
    simp [smDtTcrChallengerCheck]
  have hTcrLt : smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams B_tcr <
      prodToyGameCoins.length := by
    have hB : smDtTcrWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩ B_tcr =
        false := by
      unfold B_tcr bestTcrExtractorAdv
      exact hRejTcrFalse _
    cases hC : smDtTcrWithinWin crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ B_tcr
    · simp only [smDtTcrWithinWins, prodToyGameCoins, prodToyAcceptCoin, prodToyRejectCoin,
        hitCount, hB, hC, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
      omega
    · simp only [smDtTcrWithinWins, prodToyGameCoins, prodToyAcceptCoin, prodToyRejectCoin,
        hitCount, hB, hC, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
      omega
  rw [hRealCount]
  exact ⟨by decide, by decide, hTcrPos, hTcrLt⟩

theorem witness_within_game_reduction :
    ∃ (_coins : List ProdExperimentCoin) (params : PqHashParams) (qh qs_max : Nat)
      (A : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig)),
      (params.w = 4 ∨ params.w = 16) ∧
      (∀ pk, (A pk).Within qh qs_max) :=
  ⟨prodToyGameCoins, prodToyStatefulParams, 0, 0, prodToyForgerAdv, prodToyRadix,
    prodToyForgerAdv_within⟩

theorem witness_smDtTcr_discharges_break :
    ∃ (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
      (B : PqPublicKey → HashSignAdv (Option SmDtTcrSubmission)),
      smDtTcrWithinWin suite params sk B = true := by
  have hToyTcrEv :
      (let r := runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
        (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩))
      prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix ⟨⟨[], [], []⟩, r.2, r.1.1, r.1.2⟩
        (runHashSignAdv_queries_oneTime crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)))) =
        true := by
    have hEqEv :
        (let r := runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩))
        prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix ⟨⟨[], [], []⟩, r.2, r.1.1, r.1.2⟩
          (runHashSignAdv_queries_oneTime crumbToySuite prodToyStatefulParams ⟨[], [], []⟩
            (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)))) =
        prodTcrEvent crumbToySuite prodToyStatefulParams prodToyRadix
          ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime := rfl
    rw [hEqEv]
    unfold prodTcrEvent
    cases hOut : prodTcrOutput crumbToySuite prodToyStatefulParams prodToyRadix
        ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime with
    | none =>
      have hc := prodToyForgery_returns_collision
      rw [hOut] at hc; cases hc
    | some p =>
      exact (prodTcrOutput_sound crumbToySuite prodToyStatefulParams prodToyRadix
        ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime p.1 p.2 hOut).2.2.2
  obtain ⟨slot, hSlotWin⟩ := prodTcrEvent_captured_by_slot crumbToySuite prodToyStatefulParams
    prodToyRadix (qh := 0) (qs_max := 0) ⟨[], [], []⟩ prodToyForgerAdv prodToyForgerAdv_within
    hToyTcrEv
  exact ⟨crumbToySuite, prodToyStatefulParams, ⟨[], [], []⟩,
    tcrExtractorAdv prodToyStatefulParams slot.val prodToyForgerAdv, hSlotWin⟩

end Qsag

end

#verify_constructive Qsag.prodToyGameCoins_two_sided_nonvacuous

#tooth_pair Qsag.production_euf_cma_within_game_reduction_bound vs Qsag.tooth_replayed_query_loses_eufCmaWithin

#tooth_pair Qsag.smDtTcrWithinWin_discharges_prodSmTcrBreak vs Qsag.tooth_identical_input_rejected_by_smDtTcr

#verify_inhabited Qsag.production_euf_cma_within_game_reduction_bound Qsag.witness_within_game_reduction

#verify_inhabited Qsag.smDtTcrWithinWin_discharges_prodSmTcrBreak Qsag.witness_smDtTcr_discharges_break

public section

namespace Qsag

set_option autoImplicit false

/-- Concrete 8-point 2-to-1 compression `x ↦ x / 2` witnessing the gap between unbudgeted
    existential collision predicates (`ProdSmTcrBreak`-style) and `0`-query seed-withheld guessing:
    every secret target `s ∈ Fin 8` has a distinct sibling `s ⊕ 1` colliding under `x / 2` (`8 / 8`),
    whereas any fixed `0`-query guess `g : Fin 8` hits the distinct sibling of at most `1` secret `s`! -/
def twoToOneHash8 (x : Fin 8) : Nat := x.1 / 2

def unbudgetedCollisionExists8 (s : Fin 8) : Bool :=
  (List.finRange 8).any (fun x => decide (x ≠ s ∧ twoToOneHash8 x = twoToOneHash8 s))

def zeroQueryGuessHits8 (guess s : Fin 8) : Bool :=
  decide (guess ≠ s ∧ twoToOneHash8 guess = twoToOneHash8 s)

theorem tooth_unrestricted_smTcrBreak_exceeds_zero_query_tcr (guess : Fin 8) :
    ¬ (hitCount unbudgetedCollisionExists8 (List.finRange 8) ≤
        hitCount (zeroQueryGuessHits8 guess) (List.finRange 8)) := by
  revert guess
  decide +kernel

/-- Inhabitedness witness for `prodAdaptive_eufCma_to_budgeted_events` using `crumbToySuite`
    and a `0`-query `SeedWithheldEufCmaAdv` outputting `prodToyForgery`. -/
def witnessZeroQueryAdv : SeedWithheldEufCmaAdv 0 0 where
  run := fun _ => .pure ([], prodToyForgery)
  bounded := fun _ => trivial

theorem witness_prodAdaptive_eufCma_to_budgeted_events :
    ∃ (qHash qSign : Nat) (suite : TweakableHashSuite) (params : PqHashParams)
      (_ : params.w = 4 ∨ params.w = 16)
      (adv : SeedWithheldEufCmaAdv qHash qSign)
      (keyOf : Unit → PqSecretKey) (coins : List Unit),
      (∀ ω, AdaptiveOneTimeOn suite params adv (keyOf ω)) ∧
      1 ≤ hitCount (fun ω => prodEufCmaWin suite params
        (runSeedWithheldEufCma suite params adv (keyOf ω)).1) coins := by
  refine ⟨0, 0, crumbToySuite, prodToyStatefulParams, .inl rfl, witnessZeroQueryAdv,
    (fun _ => ⟨[], [], []⟩), [()], ?_, ?_⟩
  · intro _ _ qs q hMem
    dsimp only [qs, runSeedWithheldEufCma, witnessZeroQueryAdv, evalProdAdaptiveTree] at hMem
    exact nomatch hMem
  · decide +kernel

end Qsag

end

#tooth_pair Qsag.prodAdaptive_eufCma_to_budgeted_events vs Qsag.tooth_unrestricted_smTcrBreak_exceeds_zero_query_tcr

#verify_inhabited Qsag.prodAdaptive_eufCma_to_budgeted_events Qsag.witness_prodAdaptive_eufCma_to_budgeted_events

#verify_constructive Qsag.tooth_unrestricted_smTcrBreak_exceeds_zero_query_tcr
end

/-! ## Audits that read definitions of `Qsag.Math.Counting` -/

#verify_inhabited Qsag.HybridSecurity.one_use_incomparable Qsag.HybridSecurity.incomparable_inhabited
#tooth_pair Qsag.HybridSecurity.one_use_incomparable vs Qsag.HybridSecurity.two_uses_cover_third

/-! ## Pairs whose two theorems are proved in different modules -/

#verify_inhabited Qsag.production_stateful_forgery_witness Qsag.witness_production_stateful_forgery
#tooth_pair Qsag.production_euf_cma_extracted_bound vs Qsag.prodEufCmaWin_rejects_signed_message

/-! ## `prodPublicExtract` -/

#tooth_pair Qsag.prodPublicExtract_complete vs Qsag.tooth_identical_input_rejected_by_smDtTcr
