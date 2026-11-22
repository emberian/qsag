module
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa
public import Qsag.Protocol.Signing.Fips205
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HypertreeEufCma
public import Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity
public import Qsag.Protocol.Signing.ProdCollision
public import Qsag.Protocol.Signing.SignatureOutputAndCacheLaws
public import Qsag.Protocol.Signing.ProdHashReductions
public import Qsag.Protocol.Signing.FullAdaptiveEufCma
public import Qsag.Protocol.Signing.ClosedGameGuardTeeth
public import Qsag.Protocol.Signing.AdrsSeparationGuardTeeth
public import Qsag.Protocol.Signing.HulsingMultiHopReduction
public import Qsag.Protocol.Signing.ProductionJortsBaggyBounds
public import Qsag.Protocol.Signing.HybridAddrPolicyAndFullPresetSecurity
public import Qsag.Math.Counting
public import Qsag.Oracle.Keccak
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Tests.SigningTeeth

Negative and mutation witnesses (`tooth_*`), toy fixtures and the inhabitedness witnesses that
evaluate the signing definitions on them, for the modules imported below, with the
`#tooth_pair`, `#verify_inhabited` and `#verify_constructive` audit lines that pair each of
them with the theorem it guards. The fixtures `crumbToySuite`, `prodToyStatefulParams`,
`prodToyForgery`, `zeroToySuite` and `zeroToyParams` are plain definitions and stay in the
library modules. A statement that executes a sealed verifier, signer or game definition is proved
in the module that owns the definition (the `Exports for lane sig` sections and the sections after
them) and is cited, audited and paired here; this module cannot evaluate those bodies.
-/

/-! ## `Qsag.Protocol.Signing.Fips205` -/
public section
public section

namespace Qsag

set_option autoImplicit false

theorem tooth_slhDsaShake128s_m34_rejected :
    ({ slhDsaShake128s with m := 34 } : Fips205Params).wellFormed ≠ true := by
  intro h
  rw [slhDsaShake128s_m34_wellFormed_false] at h
  cases h

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
  simp only [fipsXmssSigShape_def, Bool.and_eq_true, decide_eq_true_eq] at hc
  have bad := hc.1.1.1
  simp only [List.length_append, List.length_cons, List.length_nil, hLen] at bad
  omega

theorem tooth_sha3_256_category5_rejected (ctx digest : List UInt8) :
    encodePreHashMsgPrime slhDsaShake256f .sha3_256 ctx digest = none := by
  simp [encodePreHashMsgPrime_def, preHashCompatible_def, slhDsaShake256f_n,
    FipsPreHashAlg.securityBytes_sha3_256]

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
    (evalStatelessCheckedSign zeroToySuite zeroToyParams ⟨[], [], []⟩ [] [] 1).isSome = true :=
  evalStatelessCheckedSign_zeroToy_isSome

/-- `#tooth`: Toy 16-bit WOTS profiles (`ell1 = 8, w = 4`) pass permissive `wellFormed` for fast
    unit models, but are strictly rejected by `productionWellFormed`. -/
theorem tooth_productionWellFormed_rejects_short_wots :
    compactTestParams.wellFormed = true ∧ compactTestParams.productionWellFormed = false :=
  PqHashParams.shortWots_wellFormed_not_production

/-- `#tooth`: Zero subtree height (`subtreeHeight = 0`) is rejected by `productionWellFormed`. -/
theorem tooth_productionWellFormed_rejects_zero_subtree_height :
    (⟨4, 128, 0, 1, 0, 0, 1, true⟩ : PqHashParams).productionWellFormed = false :=
  PqHashParams.zeroSubtreeHeight_not_production

/-- `#tooth`: Stateful profiles carrying non-zero FORS trees are rejected by `productionWellFormed`. -/
theorem tooth_productionWellFormed_rejects_stateful_with_fors :
    (⟨4, 128, 4, 2, 8, 4, 4, true⟩ : PqHashParams).productionWellFormed = false :=
  PqHashParams.statefulWithFors_not_production

/-- `#tooth`: Budgets exceeding `numLayers * subtreeHeight` or equal to `0` are rejected. -/
theorem tooth_productionWellFormed_rejects_invalid_budget :
    (⟨4, 128, 4, 2, 8, 4, 0, false⟩ : PqHashParams).productionWellFormed = false ∧
    (⟨4, 128, 4, 2, 8, 4, 9, false⟩ : PqHashParams).productionWellFormed = false :=
  PqHashParams.invalidBudget_not_production

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
  ⟨corduroyCustody128Params,
    (ProductionParameterProfile_iff _).mpr corduroyCustody128_productionWellFormed⟩

theorem tooth_short_model_is_not_production : ¬ ProductionParameterProfile compactTestParams := by
  intro h
  have hf := tooth_productionWellFormed_rejects_short_wots.2
  rw [ProductionParameterProfile_iff, hf] at h
  cases h

theorem tooth_production_stateless_rejects_stateful (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (h : params.statefulJorts = true) :
    verifyProductionStatelessChecked suite params pk msg sig = false := by
  simp [verifyProductionStatelessChecked_def, h]

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

/-- One layer of height one, one FORS tree of height one, `w = 4`, `ℓ₁ = 128`. -/
def crumbToyParams : PqHashParams := ⟨4, 128, 1, 1, 1, 1, 1, false⟩

/-- A well-shaped signature; under the constant suite it verifies for every message. -/
def crumbToyForgery : PqHashSig :=
  { rRand := [], msgTswCtr := 0, leafGlobalIdx := 0,
    forsOpenings := [⟨[], [[]]⟩],
    layerSigs := [⟨0, List.replicate 128 [], [[]]⟩] }

theorem crumbToyForgery_accepted :
    verifyPqHashSig crumbToySuite crumbToyParams
      (derivePublicKey crumbToySuite crumbToyParams ⟨[], [], []⟩) [] crumbToyForgery = true :=
  crumbToySuite_stateless_forgery_accepted

/-- The premises of `hypertree_forgery_break_of_signingLog` hold on a concrete instance (empty
    query list), and there the ITSR branch is excluded, so a collision or preimage witness
    results; a constant hash is neither collision resistant nor one-way. -/
theorem hypertree_forgery_break_inhabited :
    SmTcrBreak crumbToySuite crumbToyParams ⟨[], [], []⟩ [] ∨
    PreimageBreak crumbToySuite crumbToyParams ⟨[], [], []⟩ [] [] crumbToyForgery := by
  have h0 := hypertree_forgery_break_of_signingLog crumbToySuite crumbToyParams ⟨[], [], []⟩ [] []
      crumbToyForgery (.inl ⟨rfl, rfl⟩) rfl (by decide)
      (fun _ he => by rw [signingOracleLog_nil] at he; cases he)
      crumbToyForgery_accepted
  rw [signingOracleLog_nil] at h0
  rcases h0 with h | h
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
  crumbToySuite_forsItsrBreak

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
  refine ⟨toothDistinctSuite_oracle_budgetExhausted,
    toothDistinctSuite_oracle_equivocationRefused, ?_⟩
  have hTV : toothStatefulParams.checkedStatefulValid = true :=
    toothStatefulParams_checkedStatefulValid.1
  obtain ⟨hS1, _, hS2⟩ := toothDistinctSuite_sign_isSome
  obtain ⟨sig₁, hE1⟩ := Option.isSome_iff_exists.mp hS1
  obtain ⟨sig₂, hE2⟩ := Option.isSome_iff_exists.mp hS2
  have hE1' : evalSingleSign toothDistinctSuite toothStatefulParams ⟨[], [], []⟩ [1]
      (buildStatefulDetOptDomain 0 []) (0 % 2 ^ toothStatefulParams.maxSigsLog2) 1 = some sig₁ := by
    rw [buildStatefulDetOptDomain_def]; exact hE1
  have hE2' : evalSingleSign toothDistinctSuite toothStatefulParams ⟨[], [], []⟩ [2]
      (buildStatefulDetOptDomain 2 []) (2 % 2 ^ toothStatefulParams.maxSigsLog2) 1 = some sig₂ := by
    rw [buildStatefulDetOptDomain_def]; exact hE2
  have hM1 : mutantUncheckedReuseSign suite params sk initCheckedStatefulLatch 0 [1] 1 =
      .ok (initCheckedStatefulLatch, 0, [1], sig₁) :=
    mutantUncheckedReuseSign_ok toothDistinctSuite toothStatefulParams ⟨[], [], []⟩
      initCheckedStatefulLatch 0 [1] 1 sig₁ hTV hE1'
  have hM2 : mutantUncheckedReuseSign suite params sk initCheckedStatefulLatch 2 [2] 1 =
      .ok (initCheckedStatefulLatch, 0, [2], sig₂) :=
    mutantUncheckedReuseSign_ok toothDistinctSuite toothStatefulParams ⟨[], [], []⟩
      initCheckedStatefulLatch 2 [2] 1 sig₂ hTV hE2'
  have hSig1Idx : sig₁.leafGlobalIdx = 0 :=
    (evalSingleSign_stateful_inv toothDistinctSuite toothStatefulParams ⟨[], [], []⟩ [1]
      (buildStatefulDetOptDomain 0 []) (0 % 2 ^ toothStatefulParams.maxSigsLog2) 1 sig₁ rfl
      hE1').2.2.2.2.1
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
    exact toothDistinctSuite_star_targetSum
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
    dsimp only [suite, params, sk]
    rw [hSig1Idx]
    exact toothDistinctSuite_reuse_dominance sig₁ sig₂ hE1 hE2
  obtain ⟨hVerStar, hChainsStar, hNoWots⟩ :=
    mutantUncheckedReuseSign_collision_free_forgery suite params sk
      [3] [3] 0 hM1 hM2 (by decide) hTsw3 hDom3
  refine ⟨initCheckedStatefulLatch, initCheckedStatefulLatch, sig₁, sig₂, ?_⟩
  refine ⟨hM1, hM2, by decide, ?_⟩
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

/-- The checked oracle run on `inhabitedStatefulQueries`: three signatures, four log entries. -/
theorem inhabitedStatefulRun_eq :
    ∃ s1 s2 s3 : PqHashSig,
      execCheckedStatefulOracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
        initCheckedStatefulLatch inhabitedStatefulQueries =
        { activeState := some ⟨3, some (2, [30], s3)⟩, abortError := none,
          emittedLog := [(0, [10], s1), (1, [20], s2), (1, [20], s2), (2, [30], s3)] } :=
  crumbToySuite_twoLayer_checkedStateful_run

theorem inhabitedStatefulRun_fresh :
    ([99] : List UInt8) ∉
      ((execCheckedStatefulOracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
        initCheckedStatefulLatch inhabitedStatefulQueries).emittedLog.map fun e => e.2.1) := by
  obtain ⟨s1, s2, s3, hRun⟩ := inhabitedStatefulRun_eq
  rw [hRun]
  change ([99] : List UInt8) ∈ [[10], [20], [20], [30]] → False
  decide

theorem inhabitedStatefulForgery_accepted :
    verifyCheckedStateful crumbToySuite inhabitedStatefulParams
      (derivePublicKey crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩) [99]
      inhabitedStatefulForgery = true :=
  crumbToySuite_twoLayer_forgery_accepted

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
    inhabitedStatefulRun_fresh
    inhabitedStatefulForgery_accepted

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
  obtain ⟨s1, s2, s3, hRun⟩ := inhabitedStatefulRun_eq
  have hLog : (execCheckedStatefulOracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
      initCheckedStatefulLatch inhabitedStatefulQueries).emittedLog =
      [(0, [10], s1), (1, [20], s2), (1, [20], s2), (2, [30], s3)] :=
    congrArg CheckedStatefulOracleRun.emittedLog hRun
  refine ⟨congrArg CheckedStatefulOracleRun.abortError hRun, ?_,
          congrArg List.length hLog, congrArg (List.map Prod.fst) hLog,
          congrArg (List.map fun e => e.2.1) hLog, ?_,
          inhabitedStatefulRun_fresh, inhabitedStatefulForgery_accepted, ?_⟩
  · refine ⟨⟨3, some (2, [30], s3)⟩, ?_, rfl⟩
    rw [hLog]
    exact ((execCheckedStatefulStrict_eq_oracle crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
      inhabitedStatefulQueries initCheckedStatefulLatch).1 _ _).mpr hRun
  · intro e he
    exact checkedStatefulOracle_accepts crumbToySuite inhabitedStatefulParams ⟨[], [], []⟩
      inhabitedStatefulQueries he
  · cases inhabited_checked_stateful_multi_sign_extract with
    | inl col => exact .inl ⟨col⟩
    | inr wots => exact .inr ⟨wots⟩

/-- The latch invariant has a concrete occupied state, not just an empty log. -/
theorem witness_occupied_epoch_latch : ∃ st : EpochLatchState, st.WellFormed := by
  refine ⟨⟨1, some (0, [], ⟨[], 0, 0, [], []⟩)⟩, (EpochLatchState.wellFormed_iff _).mpr ?_⟩
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
    ⟨1, some (0, [], ⟨[], 0, 0, [], []⟩)⟩, ⟨[], 0, 0, [], []⟩,
    (EpochLatchState.wellFormed_iff _).mpr ?_, ?_⟩
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
      (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩) [] prodToyForgery = true :=
  prodToyForgery_accepted_on []

theorem prodToyStatefulParams_w : prodToyStatefulParams.w = 4 := by
  rw [prodToyStatefulParams.public_eq_1]

theorem prodToyStatefulParams_stateful : prodToyStatefulParams.statefulJorts = true := by
  rw [prodToyStatefulParams.public_eq_1]

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
  ⟨prodToyForgery, .inl prodToyStatefulParams_w, prodToyStatefulParams_stateful,
    (fun _ h => by cases h), (fun _ h => by cases h), prodToyForgery_accepted⟩

/-- On that instance the reduction returns a break of the constant hash. -/
theorem production_forgery_break_inhabited :
    ProdSmTcrBreak crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] ∨
    ProdPreimageBreak crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] [] prodToyForgery :=
  production_stateful_forgery_break crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] []
    prodToyForgery (.inl prodToyStatefulParams_w) prodToyStatefulParams_stateful
    (fun _ h => by cases h) (fun _ h => by cases h)
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
    (honestSignSubtree_length_eq_size H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs₁ hVal).trans hSz
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
        dsimp only [forgedVals, v₀]; rw [hFN, hHV, hO₁, hO₂]
        rw [runFrontierStackLoop.public_eq_2, runFrontierStackLoop.public_eq_2]
        simp only [List.headD_cons, List.tail_cons, Nat.sub_zero]
        have hAdv : chainAdvance H pk.pkSeed u 0 (p.winternitzW - 1) x =
            chainAdvance H pk.pkSeed u 1 (p.winternitzW - 1 - 1) (H.chainStep pk.pkSeed u 0 x) := by
          conv => lhs; rw [show p.winternitzW - 1 = (p.winternitzW - 1 - 1) + 1 by omega]
          rw [chainAdvance.public_eq_2]
        rw [hAdv]
      rw [hStepEq]
      have hLp := runFrontierStackLoop_frontierNodes H pk.pkSeed p.winternitzW tr 1 offs₁ honestVals
        [] [] [] [] (by decide) (hOLen₁.trans hSz.symm) (hHLen.trans hSz.symm)
      simp only [List.append_nil] at hLp
      rw [hLp, runFrontierStackLoop.public_eq_1, collapseFrontierStack.public_eq_1]
      rw [evalAntichainTree_honestSignSubtree H pk.pkSeed sk.skSeed p.winternitzW (by omega) p.treeHeight 1 tr offs₁
        (by decide) hVal (hOLen₁.trans hSz.symm)
        (fun a ha => by rw [List.mem_replicate] at ha; rw [ha.2]; omega)
        (fun hLf => by subst hLf; rw [AntichainTree.size_leaf] at hSz; omega)]
      simp [pk, deriveFrontierPk.public_eq_1]

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
    rw [signFrontierFts.public_eq_1]
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hCtr0 h))]
    simp [pk₀, msg, d, rand, rk, hUnr, sig]
  refine ⟨⟨⟨0, pk₀.root⟩, forgedDigest, sig⟩, rfl, hDiff, ?_⟩
  rw [verifyRotatedEpochVote.public_eq_1]
  have hC1 : (p.nodeBytes != 32 || p.maxSafeUses != 1) = false := by rw [hBytes, hUses]; rfl
  have hC2 : ((0 : UInt64) != 0 || (0 : UInt64).toNat + 1 >= 2 ^ 64) = false := by decide +kernel
  have hC3 : (forgedDigest != forgedDigest) = false := by simp
  simp only [hC1, hC2, hC3, Bool.false_eq_true, ↓reduceIte]
  rw [verifyFrontierFts_signFrontierFts H p hw hL skStatic hedge 0 msg sig hSign]
  simp [pk₀, deriveFrontierPk.public_eq_1]

theorem tooth_corduroy_t_corrupted_custodians_uniquely_pin_secret
    (P Q : List Goldilocks)
    (hP : verifyShamirPolyConsistent 2 P [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] = true)
    (hQ : verifyShamirPolyConsistent 2 Q [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] = true) :
    ∃ sPinned : Goldilocks,
      sPinned ≠ Goldilocks.zero ∧
      RoundPoly.evalCoeffs P Goldilocks.zero = sPinned ∧
      RoundPoly.evalCoeffs Q Goldilocks.zero = sPinned := by
  have hRef : verifyShamirPolyConsistent 2 [Goldilocks.ofNat 1, Goldilocks.ofNat 4]
      [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] = true := by
    rw [verifyShamirPolyConsistent_def]
    decide +kernel
  have hEqQ := shamirPolyConsistent_unique_at_zero 2 P Q [Goldilocks.ofNat 1, Goldilocks.ofNat 2]
    [Goldilocks.ofNat 5, Goldilocks.ofNat 9] (by decide +kernel) (by decide) hP hQ
  have hEqRef := shamirPolyConsistent_unique_at_zero 2 P [Goldilocks.ofNat 1, Goldilocks.ofNat 4]
    [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] (by decide +kernel) (by decide) hP hRef
  exact ⟨RoundPoly.evalCoeffs P Goldilocks.zero, by rw [hEqRef]; decide +kernel, rfl, hEqQ.symm⟩

theorem witness_compact1122_forgery :
    ∃ (H : FrontierHashSuite) (p : FrontierFtsParams) (_ : 2 ≤ p.frontierLen)
      (sk : FrontierSecretKey) (hedge₁ : BitVec 256) (ctr₁ : UInt16)
      (m₁ : List UInt8) (sig₁ : FrontierSignature),
      signFrontierFts H p sk hedge₁ ctr₁ m₁ = some sig₁ ∧
      ∃ (m₂ : List UInt8) (sig₂ : FrontierSignature),
        m₂ ≠ m₁ ∧ verifyFrontierFts H p (deriveFrontierPk H p sk) m₂ sig₂ = true :=
  compact1122_forgery_witness

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
  rotatedEpochVote_chain_witness

theorem witness_corduroy_real_params :
    ∃ params : PqHashParams,
      (params.w = 4 ∨ params.w = 16) ∧ params.statefulJorts = false :=
  ⟨corduroyPoseidon2AggParams, .inl rfl, rfl⟩

set_option maxRecDepth 32768

#tooth_pair Qsag.compact1122_one_time_euf_cma_reduction vs Qsag.tooth_drop_target_sum_allows_one_sig_forgery

#tooth_pair Qsag.rotatedEpochVote_forward_secure_chain vs Qsag.tooth_static_key_compromise_forges_historical_epoch

#tooth_pair Qsag.corduroy_threshold_stateless_euf_cma vs Qsag.tooth_corduroy_t_corrupted_custodians_uniquely_pin_secret

#verify_inhabited Qsag.compact1122_one_time_euf_cma_reduction Qsag.witness_compact1122_forgery

-- `witness_rotatedEpochVote_chain` is `rotatedEpochVote_chain_witness`, whose witness terms are
-- private to the owning module; the pair is certified there.
#verify_inhabited Qsag.rotatedEpochVote_forward_secure_chain Qsag.rotatedEpochVote_chain_witness

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
    prodToyForgery (.inl prodToyStatefulParams_w) prodToyStatefulParams_stateful
    (fun _ h => by cases h) (fun _ h => by cases h)
    prodToyForgery_accepted

end Qsag

end

public section

namespace Qsag

set_option autoImplicit false

theorem prodToyRadix : prodToyStatefulParams.w = 4 ∨ prodToyStatefulParams.w = 16 :=
  .inl prodToyStatefulParams_w

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
  have hEmpty : ∀ e, e ∉ productionSigningLog crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] := by
    rw [productionSigningLog_nil]
    intro e he
    cases he
  have hOne : prodToyForgery.layerSigs.length = 1 := by
    rw [prodToyForgery.public_eq_1]
    rfl
  refine prodTcrOutput_isSome_of_endpoints_ne crumbToySuite prodToyStatefulParams prodToyRadix
    ⟨[], [], []⟩ [] [] prodToyForgery prodToyOneTime prodToyStatefulParams_stateful
    prodToyForgery_accepted hEmpty hOne _ rfl ?_
  obtain ⟨h3, hk, hd⟩ := constantDigest1B_chain3_top_digit
  refine recoverWotsEndpoints_ne_honest_of_top_digit_empty _ _ _ _ _ _ _ _ 3 ?_ 2 ?_ ?_ ?_
  · rw [prodToyStatefulParams.public_eq_1]
    exact h3
  · rw [prodToyStatefulParams.public_eq_1]
    exact hk
  · rw [productionLayerDigest_rawHash, crumbToySuite_rawHash, prodToyStatefulParams.public_eq_1]
    exact hd
  · rw [prodToyForgery.public_eq_1]
    rfl

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
          simp only [computeXmssSubtreeRoot_eq, show UInt32.ofNat 0 = (0 : UInt32) from rfl, decide_true]

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
  simp [thNodeH_eq, thCall_eq, thPreimage_eq, lsbBiasSuite, lsbBiasRawHash,
    encodeMultiFrame, encodeByteFields, encodeListField, tagThH_eq, byteArray_toList_eq,
    leb128, leb128Aux]

private theorem lsbBiasSuitePublicKey (sk : PqSecretKey) :
    derivePublicKey lsbBiasSuite wotsSingleLayerParams sk =
      ⟨sk.pkSeed, 0x4B :: List.replicate 31 0x1B⟩ := by
  simp only [derivePublicKey, computeXmssSubtreeRoot_eq, wotsSingleLayerParams, computeMerkleNode_zero, computeMerkleNode_succ]
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
  simp [thNodeH_eq, thCall_eq, thPreimage_eq, bottomReuseSuite, bottomReuseRawHash,
    encodeMultiFrame, encodeByteFields, encodeListField, tagThH_eq, byteArray_toList_eq,
    leb128, leb128Aux]

private theorem bottomReuseSuitePublicKey (sk : PqSecretKey) :
    derivePublicKey bottomReuseSuite wotsSingleLayerParams sk =
      ⟨sk.pkSeed, 0x1B :: List.replicate 31 0x1B⟩ := by
  simp only [derivePublicKey, computeXmssSubtreeRoot_eq, wotsSingleLayerParams, computeMerkleNode_zero, computeMerkleNode_succ]
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
    simp [extractBaseWDigits_eq, checkTargetSum, sumDigits_nil, sumDigits_cons, List.range_succ] <;> decide

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

      simp [wotsSingleLayerParams, thHashMsg_eq, thPreHash_eq, thCall_eq, thPreimage_eq, encodeMultiFrame, encodeByteFields,
        encodeListField, leb128, leb128Aux, be, byteArray_toList_eq,
        computeMerkleNode_zero, 
        computeWotsPk_eq, wotsChainSteps_zero, wotsChainSteps_succ, wotsSecretBase_eq, thSecretPrf_eq,
        thTweakTl_eq, thNodeH_eq, thChainF_eq, PqHashParams.wellFormed_eq, PqHashParams.targetSum_eq,
        signatureToyDigestValidExpanded, signatureFirstDigit, signatureOddByte,
        verifyPqHashSig, verifyHypertreeLayers_nil, verifyHypertreeLayers_cons, recoverWotsPkFromSig_eq, recoverWotsEndpoints_eq,
        walkMerkleAuthPath, buildMerkleAuthPath_zero, buildMerkleAuthPath_succ, encodeAdrs, AdrsKind.toCode.public_eqs,
        tagPrf.public_eq_1, tagThF.public_eq_1, tagThH_eq, tagThTl.public_eq_1, tagHMsg.public_eq_1, tagHPre.public_eq_1, zeroAdrs.public_eq_1, lsbBiasSuite, lsbBiasRawHash] <;> decide
    exact h c
  · simp only [statisticalDistance, coinMass, natAbsDiff_def, qsum, maliciousSkipLsbZeroSampler,
      honestReferenceLsbSampler, coinTwoRand, evalSingleLayerAtCounter, ↓lsbBiasSuitePublicKey,
      firstValidCounter, firstValidCounterAux, sigChainLsb]

    simp [wotsSingleLayerParams, thHashMsg_eq, thPreHash_eq, thCall_eq, thPreimage_eq, encodeMultiFrame, encodeByteFields,
        encodeListField, leb128, leb128Aux, be, byteArray_toList_eq,
        computeMerkleNode_zero, 
        computeWotsPk_eq, wotsChainSteps_zero, wotsChainSteps_succ, wotsSecretBase_eq, thSecretPrf_eq,
        thTweakTl_eq, thChainF_eq, PqHashParams.wellFormed_eq, PqHashParams.targetSum_eq,
        signatureToyDigestValidExpanded, signatureFirstDigit, sigChainLsb, signatureOddByte,
        buildMerkleAuthPath_zero, buildMerkleAuthPath_succ, encodeAdrs, AdrsKind.toCode.public_eqs,
        tagPrf.public_eq_1, tagThF.public_eq_1, tagThTl.public_eq_1, tagHMsg.public_eq_1, tagHPre.public_eq_1, zeroAdrs.public_eq_1, lsbBiasSuite, lsbBiasRawHash] <;> decide
  · simp only [statisticalDistance, coinMass, natAbsDiff_def, qsum, maliciousSkipLsbZeroSampler,
      honestReferenceLsbSampler, coinTwoRand, evalSingleLayerAtCounter, ↓lsbBiasSuitePublicKey,
      firstValidCounter, firstValidCounterAux, sigChainLsb]

    simp [wotsSingleLayerParams, thHashMsg_eq, thPreHash_eq, thCall_eq, thPreimage_eq, encodeMultiFrame, encodeByteFields,
        encodeListField, leb128, leb128Aux, be, byteArray_toList_eq,
        computeMerkleNode_zero, 
        computeWotsPk_eq, wotsChainSteps_zero, wotsChainSteps_succ, wotsSecretBase_eq, thSecretPrf_eq,
        thTweakTl_eq, thChainF_eq, PqHashParams.wellFormed_eq, PqHashParams.targetSum_eq,
        signatureToyDigestValidExpanded, signatureFirstDigit, sigChainLsb, signatureOddByte,
        buildMerkleAuthPath_zero, buildMerkleAuthPath_succ, encodeAdrs, AdrsKind.toCode.public_eqs,
        tagPrf.public_eq_1, tagThF.public_eq_1, tagThTl.public_eq_1, tagHMsg.public_eq_1, tagHPre.public_eq_1, zeroAdrs.public_eq_1, lsbBiasSuite, lsbBiasRawHash] <;> decide

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

    simp [wotsSingleLayerParams, thHashMsg_eq, thPreHash_eq, thCall_eq, thPreimage_eq, encodeMultiFrame, encodeByteFields,
        encodeListField, leb128, leb128Aux, be, byteArray_toList_eq,
        computeMerkleNode_zero, 
        computeWotsPk_eq, wotsChainSteps_zero, wotsChainSteps_succ, wotsSecretBase_eq, thSecretPrf_eq,
        thTweakTl_eq, thNodeH_eq, thChainF_eq, PqHashParams.wellFormed_eq, PqHashParams.targetSum_eq,
        signatureToyDigestValidExpanded,
        verifyPqHashSig, verifyHypertreeLayers_nil, verifyHypertreeLayers_cons, recoverWotsPkFromSig_eq, recoverWotsEndpoints_eq,
        walkMerkleAuthPath, buildMerkleAuthPath_zero, buildMerkleAuthPath_succ, encodeAdrs, AdrsKind.toCode.public_eqs,
        tagPrf.public_eq_1, tagThF.public_eq_1, tagThH_eq, tagThTl.public_eq_1, tagHMsg.public_eq_1, tagHPre.public_eq_1, zeroAdrs.public_eq_1,
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

/-- All-zero 32-byte suite: base-4 digit sum is `0 ≠ 192`, so `prodToyForgery` is rejected at layer 0. -/
def zeroRejectToySuite : TweakableHashSuite where
  suiteId := []
  rawHash := fun _ => List.replicate 32 0x00
  rawHash_len := fun _ => List.length_replicate

theorem prodToyForgery_rejected_by_zeroSuite :
    verifyProductionPqHashSig zeroRejectToySuite prodToyStatefulParams
      (derivePublicKey zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩)
      [] prodToyForgery = false := by
  rw [prodToyStatefulParams.public_eq_1, prodToyForgery.public_eq_1]
  exact constantSuite00_production_forgery_rejected

theorem prodToyForgery_zeroSuite_cands_nil :
    (publicVerifierWithTcrCands zeroRejectToySuite prodToyStatefulParams
      (derivePublicKey zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩)
      [] [] prodToyForgery).2 = [] := by
  apply publicVerifierWithTcrCands_snd_nil_of_digest_rejected _ _ _ _ _ prodToyStatefulParams_stateful
  intro pre digits h
  rw [prodToyStatefulParams.public_eq_1] at h ⊢
  exact constantDigest00_targetSum_rejected digits h

def prodToyForgerAdv : PqPublicKey → HashSignAdv (List UInt8 × PqHashSig) :=
  fun _ => .done ([], prodToyForgery)

theorem prodToyForgerAdv_within (pk : PqPublicKey) : (prodToyForgerAdv pk).Within 0 0 :=
  HashSignAdv.Within.done _ 0 0

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
    unfold prodToyForgerAdv
    rw [eufCmaWithinWin_done]
    exact prodToyForgery_accepted
  have hRejLose : eufCmaWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩
      prodToyForgerAdv = false := by
    unfold prodToyForgerAdv
    rw [eufCmaWithinWin_done]
    exact prodToyForgery_rejected_by_zeroSuite
  have hRealCount :
      eufCmaRealWithinWins prodToyGameCoins prodToyStatefulParams prodToyForgerAdv = 3 := by
    simp [eufCmaRealWithinWins.public_eqs, prodToyGameCoins, prodToyAcceptCoin, prodToyRejectCoin,
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
          ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime := by
      have hr : runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)) =
          (([], prodToyForgery), []) := runHashSignAdv_done _ _ _ _ _
      simp only [hr]
    rw [hEqEv, prodTcrEvent_eq]
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
      rw [smDtTcrWithinWins.public_eqs]
      unfold prodToyGameCoins prodToyAcceptCoin hitCount
      dsimp only
      simp only [hSlotWin, ↓reduceIte]
      omega
    have hBestGe := bestTcrExtractorAdv_wins_ge_slot prodToyGameCoins prodToyStatefulParams 0
      prodToyForgerAdv slot
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hSlotGe1 hBestGe)
  have hRejTcrFalse : ∀ slot : Nat,
      smDtTcrWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩
        (tcrExtractorAdv prodToyStatefulParams slot prodToyForgerAdv) = false := by
    intro slot
    unfold prodToyForgerAdv
    exact smDtTcrWithinWin_tcrExtractorAdv_done_of_cands_nil zeroRejectToySuite
      prodToyStatefulParams ⟨[], [], []⟩ slot [] prodToyForgery prodToyForgery_zeroSuite_cands_nil
  have hTcrLt : smDtTcrWithinWins prodToyGameCoins prodToyStatefulParams B_tcr <
      prodToyGameCoins.length := by
    have hB : smDtTcrWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩ B_tcr =
        false := by
      obtain ⟨k, hk⟩ := bestTcrExtractorAdv_eq_slot prodToyGameCoins prodToyStatefulParams 0
        prodToyForgerAdv
      show smDtTcrWithinWin zeroRejectToySuite prodToyStatefulParams ⟨[], [], []⟩
        (bestTcrExtractorAdv prodToyGameCoins prodToyStatefulParams 0 prodToyForgerAdv) = false
      rw [hk]
      exact hRejTcrFalse k
    cases hC : smDtTcrWithinWin crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ B_tcr
    · simp only [smDtTcrWithinWins.public_eqs, prodToyGameCoins, prodToyAcceptCoin, prodToyRejectCoin,
        hitCount, hB, hC, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
      omega
    · simp only [smDtTcrWithinWins.public_eqs, prodToyGameCoins, prodToyAcceptCoin, prodToyRejectCoin,
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
          ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime := by
      have hr : runHashSignAdv crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ []
          (prodToyForgerAdv (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩)) =
          (([], prodToyForgery), []) := runHashSignAdv_done _ _ _ _ _
      simp only [hr]
    rw [hEqEv, prodTcrEvent_eq]
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

-- `tooth_replayed_query_loses_eufCmaWithin` and `tooth_identical_input_rejected_by_smDtTcr` are proved in
-- `Protocol/Signing/ProdHashReductions` (they unfold its sealed game definitions) and paired there with
-- `production_euf_cma_within_game_reduction_bound` and `smDtTcrWithinWin_discharges_prodSmTcrBreak`.

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
  have hRun : runSeedWithheldEufCma crumbToySuite prodToyStatefulParams witnessZeroQueryAdv
      ⟨[], [], []⟩ = (⟨⟨[], [], []⟩, [], [], prodToyForgery⟩, []) :=
    runSeedWithheldEufCma_pure _ _ _ _ _ _ (fun _ => rfl)
  refine ⟨0, 0, crumbToySuite, prodToyStatefulParams, prodToyRadix, witnessZeroQueryAdv,
    (fun _ => ⟨[], [], []⟩), [()], ?_, ?_⟩
  · intro _ _ qs q hMem
    rw [show qs = [] from congrArg (fun r => r.1.queries) hRun] at hMem
    exact nomatch hMem
  · have hWin : prodEufCmaWin crumbToySuite prodToyStatefulParams
        ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ = true := by
      rw [prodEufCmaWin_eq]
      dsimp only
      rw [productionSigningLog_nil, prodToyForgery_accepted]
      rfl
    simp [hitCount, hRun, hWin]

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

/-! ## Multi-Hop Standard-Model EUF-CMA, Guard Refutations & `< 2^{-128}` Production Bounds -/

#verify_constructive
  Qsag.poly257MultiLeaf_full_adaptive_forger_bound
  Qsag.pkDependentAdaptiveForger_violates_hCand
  Qsag.pkDependentAdaptiveForger_unconditional_bound
  Qsag.tswGuardSuite_full_adaptive_forger_bound
  Qsag.tooth_disabled_checkTargetSum_one_query_forges_prob_one
  Qsag.tooth_disabled_checkTargetSum_refutes_bound
  Qsag.symMerkleSuite_full_adaptive_forger_bound
  Qsag.tooth_zeroed_adrs_leaf_layer_forges_prob_one
  Qsag.tooth_zeroed_adrs_refutes_bound
  Qsag.hulsing_hop1_prfMsg_idealization
  Qsag.hulsing_hop2_prfSec_idealization
  Qsag.hulsing_hop3_ud_chain_simulation
  Qsag.hulsing_hop4a_itsr_bound
  Qsag.hulsing_hop4b_smDtTcr_precommitted_bound
  Qsag.hulsing_hop4b_openSeedTcr_tight_bound
  Qsag.hulsing_hop4c_smDtPre_interactive_bound
  Qsag.hulsing_full_multihop_euf_cma_bound
  Qsag.productionLatchedRandomizedSigner_trace_safe
  Qsag.jortsProd_classical_euf_cma_lt_2_neg_128
  Qsag.jortsProd_pq_qrom_euf_cma_lt_2_neg_128
  Qsag.baggySha3_128f_classical_euf_cma_lt_2_neg_128
  Qsag.baggySha3_128f_pq_qrom_euf_cma_lt_2_neg_128
  Qsag.corduroyProd_concrete_euf_cma_bound
  Qsag.baggyProd_concrete_euf_cma_bound
  Qsag.fips205_slhDsa128s_concrete_security_lt_2_neg_128
  Qsag.fips205_slhDsa128f_concrete_security_lt_2_neg_128

#tooth_pair Qsag.poly257MultiLeaf_full_adaptive_forger_bound vs
  Qsag.tooth_poly257MultiLeaf_unlatched_reuse_forges
#tooth_pair Qsag.pkDependentAdaptiveForger_unconditional_bound vs
  Qsag.pkDependentAdaptiveForger_violates_hCand
#tooth_pair Qsag.tswGuardSuite_full_adaptive_forger_bound vs
  Qsag.tooth_disabled_checkTargetSum_refutes_bound
#tooth_pair Qsag.symMerkleSuite_full_adaptive_forger_bound vs
  Qsag.tooth_zeroed_adrs_refutes_bound
#tooth_pair Qsag.hulsing_hop1_prfMsg_idealization vs
  Qsag.prfMsg_empty_refuted
#tooth_pair Qsag.hulsing_hop3_ud_chain_simulation vs
  Qsag.smDtUdHard_constHash_refuted
#tooth_pair Qsag.hulsing_hop4a_itsr_bound vs
  Qsag.tooth_stateful_no_explicitItsrCover
#tooth_pair Qsag.hulsing_hop4b_openSeedTcr_tight_bound vs
  Qsag.smDtOpenSeedTcrHard_constHash_refuted
#tooth_pair Qsag.productionLatchedRandomizedSigner_trace_safe vs
  Qsag.tooth_unlatched_stateful_signer_reuses_epoch
#tooth_pair Qsag.jortsProd_pq_qrom_euf_cma_lt_2_neg_128 vs
  Qsag.tooth_pq_grover_2pow64_exceeds_128bit_bound
#tooth_pair Qsag.baggySha3_128f_pq_qrom_euf_cma_lt_2_neg_128 vs
  Qsag.tooth_pq_grover_2pow64_exceeds_128bit_bound
#tooth_pair Qsag.fips205_slhDsa128f_concrete_security_lt_2_neg_128 vs
  Qsag.tooth_fips205_128f_bad_hmsg_rejected
