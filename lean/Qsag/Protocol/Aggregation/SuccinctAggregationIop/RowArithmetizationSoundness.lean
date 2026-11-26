module
/-
# Per-Signer Trace Exactness and the Symbolic Row Gate AST (`trace.rs`)

The polymorphic WOTS+C layer, hypertree and FORS sub-circuits, the 7-limb stateless XOF
sub-circuit, structured per-signer witness blocks whose residuals vanish exactly for valid
signatures (`signerTraceResiduals_sound`, `signerTraceResiduals_complete`), the `RowGate7`
AST with its degree-8 sumcheck bridge, and the public statement with boundary pinning.
-/

public import Qsag.Protocol.Aggregation.SuccinctAggregationIop.RowArithmetizationGates

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv
set_option autoImplicit false
set_option exponentiation.threshold 2048
attribute [local irreducible] verifyUpperLayers
attribute [local irreducible] computeMessageMu
attribute [local irreducible] verifyAggNativeSigStateful verifyAggNativeSigStateless

/-! ### Polymorphic WOTS+C Layer, Hypertree, FORS, `RowGate7` AST, and `K`-Signer Trace Exactness -/

private theorem shapeIte_allZero (p : Prop) [Decidable p]
    (h : allZeroGoldilocks (if p then [] else [Goldilocks.one]) = true) : p := by
  by_cases hp : p
  · exact hp
  · simp only [hp, ↓reduceIte] at h
    exact absurd h (by decide)

private theorem shapeIte_allZero_of (p : Prop) [Decidable p] (hp : p) :
    allZeroGoldilocks (if p then [] else [Goldilocks.one]) = true := by
  simp only [hp, ↓reduceIte]
  rfl

private def buildChainListWitnessPoly {DW V CW : Type}
    (mkChain : Nat → DW → V → CW) :
    List DW → List V → Nat → List CW
  | [], _, _ => []
  | _, [], _ => []
  | d :: ds, v :: values, c => mkChain c d v :: buildChainListWitnessPoly mkChain ds values (c + 1)

private def chainListResidualsPoly {DW CW RES : Type}
    (cRes : Nat → DW → CW → List RES) (badRes : List RES) :
    List DW → List CW → Nat → List RES
  | [], [], _ => []
  | d :: ds, w :: ws, c => cRes c d w ++ chainListResidualsPoly cRes badRes ds ws (c + 1)
  | [], _ :: _, _ => badRes
  | _ :: _, [], _ => badRes

private theorem chainListResidualsPoly_allZero_iff {DW V CW RES : Type}
    (mkChain : Nat → DW → V → CW)
    (cRes : Nat → DW → CW → List RES)
    (natOf : DW → Nat)
    (sigOf : CW → V)
    (endOf : CW → V)
    (walkFn : Nat → Nat → Nat → V → V)
    (badRes : List RES)
    (zeroPred : List RES → Bool)
    (dValid : DW → Prop)
    (hNil : zeroPred [] = true) (hBad : zeroPred badRes = false)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hChainIff : ∀ c d w, dValid d → (zeroPred (cRes c d w) = true ↔ w = mkChain c d (sigOf w)))
    (hEndMk : ∀ c d v, dValid d → endOf (mkChain c d v) = walkFn c (natOf d) (3 - natOf d) v) :
    ∀ (ds : List DW) (ws : List CW) (c : Nat),
      (∀ d ∈ ds, dValid d) →
      (zeroPred (chainListResidualsPoly cRes badRes ds ws c) = true ↔
        ds.length = ws.length ∧
        ws = buildChainListWitnessPoly mkChain ds (ws.map sigOf) c) ∧
      (ds.length = ws.length →
        ws = buildChainListWitnessPoly mkChain ds (ws.map sigOf) c →
        ws.map endOf = recoverEndpointsPoly walkFn (ds.map natOf) (ws.map sigOf) c)
  | [], [], _, _ => by
    dsimp only [chainListResidualsPoly, buildChainListWitnessPoly, recoverEndpointsPoly, List.map_nil]
    exact ⟨⟨fun _ => ⟨rfl, rfl⟩, fun _ => hNil⟩, fun _ _ => rfl⟩
  | [], _ :: _, _, _ => by
    dsimp only [chainListResidualsPoly]
    exact ⟨⟨fun h => (by rw [hBad] at h; cases h), fun h => absurd h.1 (Nat.succ_ne_zero _).symm⟩,
      fun h => absurd h (Nat.succ_ne_zero _).symm⟩
  | _ :: _, [], _, _ => by
    dsimp only [chainListResidualsPoly]
    exact ⟨⟨fun h => (by rw [hBad] at h; cases h), fun h => absurd h.1 (Nat.succ_ne_zero _)⟩,
      fun h => absurd h (Nat.succ_ne_zero _)⟩
  | d :: ds, w :: ws, c, hAll => by
    have hd : dValid d := hAll d (List.mem_cons_self ..)
    have hTailValid : ∀ x ∈ ds, dValid x := fun x hx => hAll x (List.mem_cons_of_mem _ hx)
    dsimp only [chainListResidualsPoly, buildChainListWitnessPoly, List.map_cons, recoverEndpointsPoly]
    have ih := chainListResidualsPoly_allZero_iff mkChain cRes natOf sigOf endOf walkFn badRes zeroPred dValid
      hNil hBad hAppend hChainIff hEndMk ds ws (c + 1) hTailValid
    rw [hAppend, Bool.and_eq_true, hChainIff c d w hd]
    refine ⟨?_, ?_⟩
    · constructor
      · rintro ⟨hw, hRest⟩
        obtain ⟨hLen, hWs⟩ := ih.1.mp hRest
        exact ⟨congrArg Nat.succ hLen, List.cons_eq_cons.mpr ⟨hw, hWs⟩⟩
      · rintro ⟨hLen, hCons⟩
        obtain ⟨hw, hWs⟩ := List.cons.inj hCons
        exact ⟨hw, ih.1.mpr ⟨Nat.succ.inj hLen, hWs⟩⟩
    · intro hLen hCons
      obtain ⟨hw, hWs⟩ := List.cons.inj hCons
      have hEnd0 : endOf w = walkFn c (natOf d) (3 - natOf d) (sigOf w) := by
        have hE := hEndMk c d (sigOf w) hd
        rw [← hw] at hE
        exact hE
      exact List.cons_eq_cons.mpr ⟨hEnd0, ih.2 (Nat.succ.inj hLen) hWs⟩

def honestWotsChainsWitness (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (digits : List Goldilocks) (sigVals : List Digest4) : List UnaryWotsChainWitness :=
  buildChainListWitnessPoly
    (fun c d v => honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx c d.val v)
    digits sigVals 0

def wotsChainsResiduals (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (digits : List Goldilocks) (ws : List UnaryWotsChainWitness) : List Goldilocks :=
  chainListResidualsPoly
    (unaryWotsChainResiduals pkSeed layer treeIdx kpIdx)
    [Goldilocks.one]
    digits ws 0

theorem wotsChainsResiduals_allZero_iff (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (digits : List Goldilocks) (ws : List UnaryWotsChainWitness)
    (hLt4 : ∀ d ∈ digits, d.val < 4) :
    (allZeroGoldilocks (wotsChainsResiduals pkSeed layer treeIdx kpIdx digits ws) = true ↔
      digits.length = ws.length ∧
      ws = honestWotsChainsWitness pkSeed layer treeIdx kpIdx digits (ws.map UnaryWotsChainWitness.sigVal)) ∧
    (digits.length = ws.length →
      ws = honestWotsChainsWitness pkSeed layer treeIdx kpIdx digits (ws.map UnaryWotsChainWitness.sigVal) →
      ws.map UnaryWotsChainWitness.endVal =
        recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx 0
          (digits.map Goldilocks.val) (ws.map UnaryWotsChainWitness.sigVal)) :=
  chainListResidualsPoly_allZero_iff
    (fun c (d : Goldilocks) v => honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx c d.val v)
    (unaryWotsChainResiduals pkSeed layer treeIdx kpIdx)
    Goldilocks.val
    UnaryWotsChainWitness.sigVal
    UnaryWotsChainWitness.endVal
    (wotsChainWalk pkSeed layer treeIdx kpIdx)
    [Goldilocks.one]
    allZeroGoldilocks
    (fun d => d.val < 4)
    rfl (by decide) allZeroGoldilocks_append
    (fun c d w hd => unaryWotsChainResiduals_allZero_iff pkSeed layer treeIdx kpIdx c d w hd)
    (fun c (d : Goldilocks) v hd => honestUnaryWotsChainWitness_endVal pkSeed layer treeIdx kpIdx c d.val v hd)
    digits ws 0 hLt4


private theorem map_sigOf_buildChainListWitnessPoly {DW V CW : Type}
    (mkChain : Nat → DW → V → CW) (sigOf : CW → V)
    (hSig : ∀ c d v, sigOf (mkChain c d v) = v) :
    ∀ (ds : List DW) (values : List V) (c : Nat),
      ds.length = values.length →
      (buildChainListWitnessPoly mkChain ds values c).map sigOf = values
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], _, h => absurd h (Nat.succ_ne_zero _)
  | d :: ds, v :: values, c, h => by
    dsimp only [buildChainListWitnessPoly]
    rw [List.map_cons, hSig, map_sigOf_buildChainListWitnessPoly mkChain sigOf hSig ds values (c + 1) (Nat.succ.inj h)]

private theorem length_buildChainListWitnessPoly {DW V CW : Type}
    (mkChain : Nat → DW → V → CW) :
    ∀ (ds : List DW) (values : List V) (c : Nat),
      ds.length = values.length →
      (buildChainListWitnessPoly mkChain ds values c).length = values.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], _, h => absurd h (Nat.succ_ne_zero _)
  | _ :: ds, _ :: values, c, h => by
    dsimp only [buildChainListWitnessPoly]
    rw [List.length_cons, length_buildChainListWitnessPoly mkChain ds values (c + 1) (Nat.succ.inj h)]
    rfl

private theorem map_sibOf_buildMerklePathWitnessPoly {D LW : Type}
    (mkLvl : Nat → Nat → D → D → LW) (parentOf sibOf : LW → D)
    (hSib : ∀ lvl idx cur sib, sibOf (mkLvl lvl idx cur sib) = sib) :
    ∀ (sibs : List D) (lvl idx : Nat) (cur : D),
      (buildMerklePathWitnessPoly mkLvl parentOf sibs lvl idx cur).map sibOf = sibs
  | [], _, _, _ => rfl
  | sib :: sibs, lvl, idx, cur => by
    dsimp only [buildMerklePathWitnessPoly]
    rw [List.map_cons, hSib, map_sibOf_buildMerklePathWitnessPoly mkLvl parentOf sibOf hSib sibs]

private theorem length_buildMerklePathWitnessPoly {D LW : Type}
    (mkLvl : Nat → Nat → D → D → LW) (parentOf : LW → D) :
    ∀ (sibs : List D) (lvl idx : Nat) (cur : D),
      (buildMerklePathWitnessPoly mkLvl parentOf sibs lvl idx cur).length = sibs.length
  | [], _, _, _ => rfl
  | _ :: sibs, lvl, idx, cur => by
    dsimp only [buildMerklePathWitnessPoly]
    rw [List.length_cons, length_buildMerklePathWitnessPoly mkLvl parentOf sibs]
    rfl

/-- Single WOTS+C + XMSS subtree layer execution trace witness (`verifyWotsLayer` sub-circuit). -/
structure WotsLayerTraceWitness where
  tswCtr   : Nat
  decomp   : Hmsg5DecompWitness
  chains   : List UnaryWotsChainWitness
  pkSponge : SpongeAbsorbWitness
  merkle   : List MerkleLevelWitness
  rootOut  : Digest4
  deriving DecidableEq, Repr

def wotsLayerWitnessSig (w : WotsLayerTraceWitness) : WotsLayerSig :=
  { tswCtr     := w.tswCtr
    wotsChains := w.chains.map UnaryWotsChainWitness.sigVal
    merklePath := w.merkle.map MerkleLevelWitness.sibling }

def honestWotsLayerTraceWitness (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (lsig : WotsLayerSig) : WotsLayerTraceWitness :=
  let dec := honestHmsg5DecompWitness hmsg
  let digitWires := hmsg5DigitWires geom dec
  let chs := honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digitWires lsig.wotsChains
  let endpoints := chs.map UnaryWotsChainWitness.endVal
  let sp := honestSpongeAbsorbWitness
    (wotsPkInitState pk.pkSeed layer treeIdx kpIdx endpoints.length) endpoints
  let mPath := honestMerklePathWitness domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest lsig.merklePath
  let rt := (merklePathResiduals domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest mPath).1
  { tswCtr := lsig.tswCtr, decomp := dec, chains := chs, pkSponge := sp, merkle := mPath, rootOut := rt }

def wotsLayerTraceResiduals (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (w : WotsLayerTraceWitness) : List Goldilocks :=
  let shapeRes :=
    if w.chains.length == geom.wotsChains && w.merkle.length == geom.subtreeHeight then []
    else [Goldilocks.one]
  let digitWires := hmsg5DigitWires geom w.decomp
  let endpoints := w.chains.map UnaryWotsChainWitness.endVal
  let (walkedRt, mRes) :=
    merklePathResiduals domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx w.pkSponge.outDigest w.merkle
  shapeRes ++
  hmsg5DecompResiduals geom hmsg w.decomp ++
  wotsChainsResiduals pk.pkSeed layer treeIdx kpIdx digitWires w.chains ++
  spongeAbsorbResiduals (wotsPkInitState pk.pkSeed layer treeIdx kpIdx endpoints.length) endpoints w.pkSponge ++
  mRes ++
  (lane4Sub w.rootOut walkedRt).toList

theorem wotsLayerTraceResiduals_sound (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (w : WotsLayerTraceWitness)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hZero : allZeroGoldilocks (wotsLayerTraceResiduals geom pk layer treeIdx kpIdx hmsg w) = true) :
    verifyWotsLayer geom pk layer treeIdx kpIdx hmsg (wotsLayerWitnessSig w) = some w.rootOut := by
  unfold wotsLayerTraceResiduals at hZero
  dsimp only at hZero
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff] at hZero
  rcases hZero with ⟨⟨⟨⟨⟨hShape, hDec⟩, hCh⟩, hSp⟩, hM⟩, hRtEq⟩
  have hLenChk := shapeIte_allZero _ hShape
  · obtain ⟨hDecEq, ds, hExt, hSum, hWiresMap⟩ :=
      (hmsg5DecompResiduals_allZero_iff geom hmsg w.decomp hChainsLe hTargetBound).mp hDec
    obtain ⟨_, hDsLt4⟩ := extractWotsDigitsChecked_spec hChainsLe hExt
    have hWiresLt4 : ∀ d ∈ hmsg5DigitWires geom w.decomp, d.val < 4 := by
      intro d hd
      have hMemMap : d.val ∈ (hmsg5DigitWires geom w.decomp).map Goldilocks.val := List.mem_map_of_mem hd
      rw [hWiresMap] at hMemMap
      exact hDsLt4 d.val hMemMap
    have hChIff := wotsChainsResiduals_allZero_iff pk.pkSeed layer treeIdx kpIdx
      (hmsg5DigitWires geom w.decomp) w.chains hWiresLt4
    obtain ⟨hDigLenEq, hChEq⟩ := hChIff.1.mp hCh
    have hEndEq := hChIff.2 hDigLenEq hChEq
    rw [hWiresMap] at hEndEq
    have hSpIff := wotsPkSpongeResiduals_allZero_iff pk.pkSeed layer treeIdx kpIdx
      (w.chains.map UnaryWotsChainWitness.endVal) w.pkSponge
    have hSpOut := hSpIff.2 (hSpIff.1.mp hSp)
    have hMIff := merklePathResiduals_allZero_iff domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx
      w.pkSponge.outDigest w.merkle
    have hWalkOut := hMIff.2 (hMIff.1.mp hM)
    simp only [verifyWotsLayer.public_eqs]
    unfold wotsLayerWitnessSig
    have hSigShape :
        ((w.chains.map UnaryWotsChainWitness.sigVal).length == geom.wotsChains &&
         (w.merkle.map MerkleLevelWitness.sibling).length == geom.subtreeHeight) = true := by
      rw [List.length_map, List.length_map, Bool.and_eq_true]; exact hLenChk
    simp only [hSigShape, ↓reduceIte, hExt, hSum, beq_self_eq_true, Option.some.injEq]
    rw [← hEndEq, ← hSpOut, ← hWalkOut, ← hRtEq]

theorem wotsLayerTraceResiduals_complete (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (lsig : WotsLayerSig) (rt : Digest4)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hVer : verifyWotsLayer geom pk layer treeIdx kpIdx hmsg lsig = some rt) :
    let w := honestWotsLayerTraceWitness geom pk layer treeIdx kpIdx hmsg lsig
    wotsLayerWitnessSig w = lsig ∧
    w.rootOut = rt ∧
    allZeroGoldilocks (wotsLayerTraceResiduals geom pk layer treeIdx kpIdx hmsg w) = true := by
  intro w
  simp only [verifyWotsLayer.public_eqs] at hVer
  cases hShape : (lsig.wotsChains.length == geom.wotsChains && lsig.merklePath.length == geom.subtreeHeight)
  · simp [hShape] at hVer
  · simp only [hShape, ↓reduceIte] at hVer
    rcases Bool.and_eq_true_iff.mp hShape with ⟨hChLenB, hMpLenB⟩
    have hChLen : lsig.wotsChains.length = geom.wotsChains := eq_of_beq hChLenB
    have hMpLen : lsig.merklePath.length = geom.subtreeHeight := eq_of_beq hMpLenB
    cases hExt : extractWotsDigitsChecked geom hmsg with
    | none => simp [hExt] at hVer
    | some ds =>
      simp only [hExt] at hVer
      cases hSumB : (listNatSum ds == geom.targetSum)
      · simp [hSumB] at hVer
      · simp only [hSumB, ↓reduceIte, Option.some.injEq] at hVer
        have hSum : listNatSum ds = geom.targetSum := eq_of_beq hSumB
        obtain ⟨hDsLen, hDsLt4⟩ := extractWotsDigitsChecked_spec hChainsLe hExt
        have hWiresMap :
            (hmsg5DigitWires geom (honestHmsg5DecompWitness hmsg)).map Goldilocks.val = ds := by
          simp only [extractWotsDigitsChecked.public_eqs] at hExt
          cases hChk : checkDigest5Limbs63 hmsg
          · simp [hChk] at hExt
          · simp only [hChk, ↓reduceIte, Option.some.injEq] at hExt
            subst hExt
            unfold hmsg5DigitWires honestHmsg5DecompWitness honestLimb63DecompWitness
            dsimp only
            simp only [List.map_take, List.map_append, map_val_ofNat_extract, take4_extractLimbBase4Digits_31]
        have hDecZero :
            allZeroGoldilocks (hmsg5DecompResiduals geom hmsg (honestHmsg5DecompWitness hmsg)) = true :=
          (hmsg5DecompResiduals_allZero_iff geom hmsg (honestHmsg5DecompWitness hmsg)
            hChainsLe hTargetBound).mpr ⟨rfl, ds, hExt, hSum, hWiresMap⟩
        let digWires := hmsg5DigitWires geom (honestHmsg5DecompWitness hmsg)
        have hDigWiresLen : digWires.length = lsig.wotsChains.length := by
          have h1 : digWires.length = ds.length := by rw [← hWiresMap, List.length_map]
          omega
        have hWiresLt4 : ∀ d ∈ digWires, d.val < 4 := by
          intro d hd
          have hm : d.val ∈ digWires.map Goldilocks.val := List.mem_map_of_mem hd
          rw [hWiresMap] at hm
          exact hDsLt4 d.val hm
        have hSigMap :
            (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).map
              UnaryWotsChainWitness.sigVal = lsig.wotsChains :=
          map_sigOf_buildChainListWitnessPoly
            (fun c (d : Goldilocks) v => honestUnaryWotsChainWitness pk.pkSeed layer treeIdx kpIdx c d.val v)
            UnaryWotsChainWitness.sigVal (fun _ _ _ => rfl) digWires lsig.wotsChains 0 hDigWiresLen
        have hChsLen :
            (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).length =
              geom.wotsChains := by
          unfold honestWotsChainsWitness
          rw [length_buildChainListWitnessPoly _ digWires lsig.wotsChains 0 hDigWiresLen, hChLen]
        have hSibMap :
            ∀ (cur : Digest4),
              (honestMerklePathWitness domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx cur lsig.merklePath).map
                MerkleLevelWitness.sibling = lsig.merklePath :=
          fun cur => map_sibOf_buildMerklePathWitnessPoly _ _ _ (fun _ _ _ _ => rfl) lsig.merklePath 1 kpIdx cur
        have hMpWLen :
            ∀ (cur : Digest4),
              (honestMerklePathWitness domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx cur lsig.merklePath).length =
                geom.subtreeHeight := by
          intro cur
          unfold honestMerklePathWitness
          rw [length_buildMerklePathWitnessPoly, hMpLen]
        have hSigEq : wotsLayerWitnessSig w = lsig := by
          rcases lsig with ⟨ctr, chs, mp⟩
          unfold wotsLayerWitnessSig
          dsimp only [w, honestWotsLayerTraceWitness]
          simp only [WotsLayerSig.mk.injEq]
          exact ⟨trivial, hSigMap, hSibMap _⟩
        have hChIff := wotsChainsResiduals_allZero_iff pk.pkSeed layer treeIdx kpIdx
          digWires (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains) hWiresLt4
        have hChZero :
            allZeroGoldilocks (wotsChainsResiduals pk.pkSeed layer treeIdx kpIdx digWires
              (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains)) = true := by
          apply hChIff.1.mpr
          refine ⟨?_, ?_⟩
          · rw [hChsLen, ← hChLen]; exact hDigWiresLen
          · rw [hSigMap]
        have hEndEq :
            (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).map
              UnaryWotsChainWitness.endVal =
            recoverAggWotsEndpoints pk.pkSeed layer treeIdx kpIdx 0 ds lsig.wotsChains := by
          have e0 := hChIff.2 (by rw [hChsLen, ← hChLen]; exact hDigWiresLen) (by rw [hSigMap])
          rw [hWiresMap, hSigMap] at e0
          exact e0
        let eps := (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).map
          UnaryWotsChainWitness.endVal
        let sp := honestSpongeAbsorbWitness (wotsPkInitState pk.pkSeed layer treeIdx kpIdx eps.length) eps
        have hSpIff := wotsPkSpongeResiduals_allZero_iff pk.pkSeed layer treeIdx kpIdx eps sp
        have hSpZero :
            allZeroGoldilocks (spongeAbsorbResiduals (wotsPkInitState pk.pkSeed layer treeIdx kpIdx eps.length) eps sp) = true :=
          hSpIff.1.mpr rfl
        have hSpOut : sp.outDigest =
            compressWotsEndpointsSponge pk.pkSeed layer treeIdx kpIdx
              (recoverAggWotsEndpoints pk.pkSeed layer treeIdx kpIdx 0 ds lsig.wotsChains) := by
          rw [hSpIff.2 rfl]
          exact congrArg _ hEndEq
        let mPath := honestMerklePathWitness domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest lsig.merklePath
        have hMIff := merklePathResiduals_allZero_iff domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest mPath
        have hMZero :
            allZeroGoldilocks (merklePathResiduals domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest mPath).2 = true :=
          hMIff.1.mpr (by rw [hSibMap])
        have hWalkEq :
            (merklePathResiduals domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest mPath).1 = rt := by
          rw [hMIff.2 (by rw [hSibMap]), hSibMap, hSpOut, hVer]
        refine ⟨hSigEq, hWalkEq, ?_⟩
        unfold wotsLayerTraceResiduals
        dsimp only [w, honestWotsLayerTraceWitness]
        have hWShape :
            ((honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).length == geom.wotsChains &&
             mPath.length == geom.subtreeHeight) = true := by
          rw [hChsLen, hMpWLen]; simp
        simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff]
        exact ⟨⟨⟨⟨⟨shapeIte_allZero_of _ (Bool.and_eq_true_iff.mp hWShape), hDecZero⟩, hChZero⟩, hSpZero⟩,
          hMZero⟩, trivial⟩

/-- Single upper-hypertree layer trace node (`HmsgDetTree` + `WotsLayerTraceWitness`). -/
structure UpperLayerTraceNode where
  detHmsg  : HmsgDetTreeTraceWitness
  wotsStep : WotsLayerTraceWitness
  deriving DecidableEq, Repr

private def buildUpperTracePoly {D LS NW : Type}
    (mkNode : Nat → Nat → D → LS → (Nat × D × NW)) :
    List LS → Nat → Nat → D → List NW
  | [], _, _, _ => []
  | lsig :: rest, layer, rem, curRt =>
    let (nextRem, nextRt, nw) := mkNode layer rem curRt lsig
    nw :: buildUpperTracePoly mkNode rest (layer + 1) nextRem nextRt

private def upperTraceResidualsPoly {D NW RES : Type}
    (nodeRes : Nat → Nat → D → NW → (Nat × D × List RES)) :
    List NW → Nat → Nat → D → (D × List RES)
  | [], _, _, curRt => (curRt, [])
  | nw :: rest, layer, rem, curRt =>
    let (nextRem, nextRt, r0) := nodeRes layer rem curRt nw
    let (topRt, restRes) := upperTraceResidualsPoly nodeRes rest (layer + 1) nextRem nextRt
    (topRt, r0 ++ restRes)

private theorem upperTraceResidualsPoly_sound {D LS NW RES : Type}
    (nodeRes : Nat → Nat → D → NW → (Nat × D × List RES))
    (vStep : Nat → Nat → D → LS → Option (Nat × D))
    (sigOf : NW → LS)
    (zeroPred : List RES → Bool)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hNodeSound : ∀ layer rem cur nw,
      zeroPred (nodeRes layer rem cur nw).2.2 = true →
      vStep layer rem cur (sigOf nw) = some ((nodeRes layer rem cur nw).1, (nodeRes layer rem cur nw).2.1)) :
    ∀ (nws : List NW) (layer rem : Nat) (curRt : D),
      zeroPred (upperTraceResidualsPoly nodeRes nws layer rem curRt).2 = true →
      verifyUpperPoly vStep (nws.map sigOf) layer rem curRt =
        some (upperTraceResidualsPoly nodeRes nws layer rem curRt).1
  | [], _, _, _, _ => rfl
  | nw :: rest, layer, rem, curRt, hZ => by
    dsimp only [upperTraceResidualsPoly] at hZ ⊢
    rw [List.map_cons]
    dsimp only [verifyUpperPoly]
    rw [hAppend, Bool.and_eq_true] at hZ
    rw [hNodeSound layer rem curRt nw hZ.1]
    exact upperTraceResidualsPoly_sound nodeRes vStep sigOf zeroPred hAppend hNodeSound
      rest (layer + 1) (nodeRes layer rem curRt nw).1 (nodeRes layer rem curRt nw).2.1 hZ.2

private theorem upperTraceResidualsPoly_complete {D LS NW RES : Type}
    (mkNode : Nat → Nat → D → LS → (Nat × D × NW))
    (nodeRes : Nat → Nat → D → NW → (Nat × D × List RES))
    (vStep : Nat → Nat → D → LS → Option (Nat × D))
    (sigOf : NW → LS)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hNodeComplete : ∀ layer rem cur lsig nr nrt,
      vStep layer rem cur lsig = some (nr, nrt) →
      let out := mkNode layer rem cur lsig
      out.1 = nr ∧ out.2.1 = nrt ∧ sigOf out.2.2 = lsig ∧
      (nodeRes layer rem cur out.2.2).1 = nr ∧
      (nodeRes layer rem cur out.2.2).2.1 = nrt ∧
      zeroPred (nodeRes layer rem cur out.2.2).2.2 = true) :
    ∀ (ls : List LS) (layer rem : Nat) (curRt topRt : D),
      verifyUpperPoly vStep ls layer rem curRt = some topRt →
      let nws := buildUpperTracePoly mkNode ls layer rem curRt
      nws.map sigOf = ls ∧
      (upperTraceResidualsPoly nodeRes nws layer rem curRt).1 = topRt ∧
      zeroPred (upperTraceResidualsPoly nodeRes nws layer rem curRt).2 = true
  | [], _, _, _, _, hVer => by
    dsimp only [verifyUpperPoly, buildUpperTracePoly, upperTraceResidualsPoly, List.map_nil] at hVer ⊢
    injection hVer with hEq
    exact ⟨rfl, hEq, hNil⟩
  | lsig :: rest, layer, rem, curRt, topRt, hVer => by
    dsimp only [verifyUpperPoly] at hVer
    cases hSt : vStep layer rem curRt lsig with
    | none => simp [hSt] at hVer
    | some pair =>
      rcases pair with ⟨nr, nrt⟩
      simp only [hSt] at hVer
      obtain ⟨hMk1, hMk2, hSig, hRes1, hRes2, hResZ⟩ := hNodeComplete layer rem curRt lsig nr nrt hSt
      obtain ⟨ihMap, ihTop, ihZ⟩ := upperTraceResidualsPoly_complete mkNode nodeRes vStep sigOf
        zeroPred hNil hAppend hNodeComplete rest (layer + 1) nr nrt topRt hVer
      dsimp only [buildUpperTracePoly]
      obtain ⟨m1, m2, mnw, hMkEq⟩ : ∃ m1 m2 mnw, mkNode layer rem curRt lsig = (m1, m2, mnw) := ⟨_, _, _, rfl⟩
      rw [hMkEq] at hMk1 hMk2 hSig hRes1 hRes2 hResZ ⊢
      dsimp only at hMk1 hMk2 hSig hRes1 hRes2 hResZ ⊢
      subst hMk1 hMk2
      dsimp only [List.map_cons, upperTraceResidualsPoly]
      rw [hRes1, hRes2, hAppend, Bool.and_eq_true]
      exact ⟨List.cons_eq_cons.mpr ⟨hSig, ihMap⟩, ihTop, ⟨hResZ, ihZ⟩⟩


def honestUpperLayersTrace (geom : AggSigGeometry) (pk : AggValidatorPk)
    (startLayer remIdx : Nat) (curRt : Digest4) (ls : List WotsLayerSig) : List UpperLayerTraceNode :=
  buildUpperTracePoly
    (fun l rem cur lsig =>
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let dh := honestHmsgDetTreeTraceWitness pk l treeIdx kpIdx lsig.tswCtr cur
      let wl := honestWotsLayerTraceWitness geom pk l treeIdx kpIdx dh.outMsg lsig
      (treeIdx, wl.rootOut, { detHmsg := dh, wotsStep := wl }))
    ls startLayer remIdx curRt

def upperLayersTraceResiduals (geom : AggSigGeometry) (pk : AggValidatorPk)
    (startLayer remIdx : Nat) (curRt : Digest4) (nws : List UpperLayerTraceNode) :
    (Digest4 × List Goldilocks) :=
  upperTraceResidualsPoly
    (fun l rem cur nw =>
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let rH := hmsgDetTreeResiduals pk l treeIdx kpIdx nw.wotsStep.tswCtr cur nw.detHmsg
      let rW := wotsLayerTraceResiduals geom pk l treeIdx kpIdx nw.detHmsg.outMsg nw.wotsStep
      (treeIdx, nw.wotsStep.rootOut, rH ++ rW))
    nws startLayer remIdx curRt

theorem upperLayersTraceResiduals_sound (geom : AggSigGeometry) (pk : AggValidatorPk)
    (startLayer remIdx : Nat) (curRt : Digest4) (nws : List UpperLayerTraceNode)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hZero : allZeroGoldilocks (upperLayersTraceResiduals geom pk startLayer remIdx curRt nws).2 = true) :
    verifyUpperLayers geom pk startLayer remIdx curRt
      (nws.map fun nw => wotsLayerWitnessSig nw.wotsStep) =
      some (upperLayersTraceResiduals geom pk startLayer remIdx curRt nws).1 := by
  unfold upperLayersTraceResiduals at hZero ⊢
  unfold verifyUpperLayers
  refine upperTraceResidualsPoly_sound _ _ (fun (nw : UpperLayerTraceNode) => wotsLayerWitnessSig nw.wotsStep)
    allZeroGoldilocks allZeroGoldilocks_append ?_ nws startLayer remIdx curRt hZero
  intro l rem cur nw hNodeZ
  dsimp only at hNodeZ ⊢
  rw [allZeroGoldilocks_append, Bool.and_eq_true] at hNodeZ
  have hDetIff := hmsgDetTreeResiduals_allZero_iff pk l (rem / 2 ^ geom.subtreeHeight)
    (rem % 2 ^ geom.subtreeHeight) nw.wotsStep.tswCtr cur nw.detHmsg
  have hOutMsg := hDetIff.2 (hDetIff.1.mp hNodeZ.1)
  have hWSound := wotsLayerTraceResiduals_sound geom pk l (rem / 2 ^ geom.subtreeHeight)
    (rem % 2 ^ geom.subtreeHeight) nw.detHmsg.outMsg nw.wotsStep hChainsLe hTargetBound hNodeZ.2
  have hCtr : (wotsLayerWitnessSig nw.wotsStep).tswCtr = nw.wotsStep.tswCtr := rfl
  rw [hCtr, ← hOutMsg, hWSound]

theorem upperLayersTraceResiduals_complete (geom : AggSigGeometry) (pk : AggValidatorPk)
    (startLayer remIdx : Nat) (curRt topRt : Digest4) (ls : List WotsLayerSig)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hVer : verifyUpperLayers geom pk startLayer remIdx curRt ls = some topRt) :
    let nws := honestUpperLayersTrace geom pk startLayer remIdx curRt ls
    (nws.map fun nw => wotsLayerWitnessSig nw.wotsStep) = ls ∧
    (upperLayersTraceResiduals geom pk startLayer remIdx curRt nws).1 = topRt ∧
    allZeroGoldilocks (upperLayersTraceResiduals geom pk startLayer remIdx curRt nws).2 = true := by
  unfold verifyUpperLayers at hVer
  unfold honestUpperLayersTrace upperLayersTraceResiduals
  refine upperTraceResidualsPoly_complete _ _ _ (fun (nw : UpperLayerTraceNode) => wotsLayerWitnessSig nw.wotsStep)
    allZeroGoldilocks rfl allZeroGoldilocks_append ?_ ls startLayer remIdx curRt topRt hVer
  intro l rem cur lsig nr nrt hSt
  dsimp only at hSt ⊢
  let kpIdx := rem % (2 ^ geom.subtreeHeight)
  let treeIdx := rem / (2 ^ geom.subtreeHeight)
  let hmsg := computeHmsgDetTree pk l treeIdx kpIdx lsig.tswCtr cur
  change (match verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
          | none => none | some nextRoot => some (treeIdx, nextRoot)) = some (nr, nrt) at hSt
  cases hW : verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
  | none => rw [hW] at hSt; cases hSt
  | some rtOut =>
    rw [hW] at hSt
    simp only [Option.some.injEq, Prod.mk.injEq] at hSt
    rcases hSt with ⟨hNr, hNrt⟩
    subst hNr hNrt
    let dh := honestHmsgDetTreeTraceWitness pk l treeIdx kpIdx lsig.tswCtr cur
    have hDetIff := hmsgDetTreeResiduals_allZero_iff pk l treeIdx kpIdx lsig.tswCtr cur dh
    have hDhOut : dh.outMsg = hmsg := hDetIff.2 rfl
    have hDhZero : allZeroGoldilocks (hmsgDetTreeResiduals pk l treeIdx kpIdx lsig.tswCtr cur dh) = true :=
      hDetIff.1.mpr rfl
    have hWSub : verifyWotsLayer geom pk l treeIdx kpIdx dh.outMsg lsig = some rtOut := by
      rw [hDhOut]; exact hW
    obtain ⟨hWSig, hWRt, hWZero⟩ := wotsLayerTraceResiduals_complete geom pk l treeIdx kpIdx
      dh.outMsg lsig rtOut hChainsLe hTargetBound hWSub
    have hCtrEq : (honestWotsLayerTraceWitness geom pk l treeIdx kpIdx dh.outMsg lsig).tswCtr = lsig.tswCtr := rfl
    refine ⟨rfl, hWRt, hWSig, rfl, hWRt, ?_⟩
    rw [allZeroGoldilocks_append, Bool.and_eq_true, hCtrEq]
    exact ⟨hDhZero, hWZero⟩


/-! ### FORS Opening Sub-Circuit & 7-Limb `< 2^63` Stateless XOF Sub-Circuit -/

private theorem forsLeafHash_eq_perm (geom : AggSigGeometry) (pkSeed val : Digest4)
    (leafGlobalIdx j idx : Nat) :
    forsLeafHash geom pkSeed val leafGlobalIdx j idx =
      lane4Add (poseidon2Perm12
        ⟨val, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx j idx⟩).b0
        (poseidon2WeightedFeedForward
          ⟨val, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx j idx⟩) := by
  simp only [forsLeafHash.public_eqs, poseidon2Compress12FF.public_eqs]
  rw [poseidon2CompressWeighted_eq]

structure ForsOpeningTraceWitness where
  secretVal : Digest4
  leafPerm  : Poseidon2PermWitness
  merkle    : List MerkleLevelWitness
  treeRoot  : Digest4
  deriving DecidableEq, Repr

def forsOpeningWitnessSig (w : ForsOpeningTraceWitness) : AggForsTreeOpening :=
  { secretVal := w.secretVal
    authPath  := w.merkle.map MerkleLevelWitness.sibling }

def honestForsOpeningTraceWitness (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx t idx : Nat)
    (op : AggForsTreeOpening) : ForsOpeningTraceWitness :=
  let lp := honestPoseidon2PermWitness ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩
  let leaf := lane4Add lp.output.b0
      (poseidon2WeightedFeedForward
        ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩)
  let mp := honestMerklePathWitness domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf op.authPath
  let rt := (merklePathResiduals domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf mp).1
  { secretVal := op.secretVal, leafPerm := lp, merkle := mp, treeRoot := rt }

def forsOpeningResiduals (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx t idx : Nat) (w : ForsOpeningTraceWitness) : List Goldilocks :=
  let shapeRes :=
    if decide (idx < 2 ^ geom.forsHeight) && (w.merkle.length == geom.forsHeight) then []
    else [Goldilocks.one]
  let leaf := lane4Add w.leafPerm.output.b0
      (poseidon2WeightedFeedForward
        ⟨w.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩)
  let (walkedRt, mRes) := merklePathResiduals domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf w.merkle
  shapeRes ++
  permWithInputResiduals ⟨w.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩ w.leafPerm ++
  mRes ++
  (lane4Sub w.treeRoot walkedRt).toList

theorem forsOpeningResiduals_sound (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx t idx : Nat) (w : ForsOpeningTraceWitness)
    (hZero : allZeroGoldilocks (forsOpeningResiduals geom pkSeed leafGlobalIdx t idx w) = true) :
    verifySingleForsOpening geom pkSeed leafGlobalIdx t idx (forsOpeningWitnessSig w) = some w.treeRoot := by
  unfold forsOpeningResiduals at hZero
  dsimp only at hZero
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, permWithInputResiduals_allZero_iff,
    lane4Sub_toList_allZero_iff] at hZero
  rcases hZero with ⟨⟨⟨hShape, hLp⟩, hM⟩, hRtEq⟩
  have hChk := shapeIte_allZero _ hShape
  · have hPermOut : (honestPoseidon2PermWitness ⟨w.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩).output =
        poseidon2Perm12 ⟨w.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩ := by
      unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
    have hLeafEq : lane4Add w.leafPerm.output.b0
      (poseidon2WeightedFeedForward
        ⟨w.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩) =
        forsLeafHash geom pkSeed w.secretVal leafGlobalIdx t idx := by
      rw [hLp, hPermOut, forsLeafHash_eq_perm]
    have hMIff := merklePathResiduals_allZero_iff domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx
      (lane4Add w.leafPerm.output.b0
      (poseidon2WeightedFeedForward
        ⟨w.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩)) w.merkle
    have hWalkEq := hMIff.2 (hMIff.1.mp hM)
    simp only [verifySingleForsOpening.public_eqs]
    unfold forsOpeningWitnessSig
    rcases hChk with ⟨hIdxDec, hMpLenB⟩
    have hIdxLt : idx < 2 ^ geom.forsHeight := of_decide_eq_true hIdxDec
    simp only [hIdxLt, decide_true, List.length_map, hMpLenB, Bool.true_and, ↓reduceIte, Option.some.injEq]
    rw [hRtEq, hWalkEq, hLeafEq]

theorem forsOpeningResiduals_complete (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx t idx : Nat) (op : AggForsTreeOpening) (rt : Digest4)
    (hVer : verifySingleForsOpening geom pkSeed leafGlobalIdx t idx op = some rt) :
    let w := honestForsOpeningTraceWitness geom pkSeed leafGlobalIdx t idx op
    forsOpeningWitnessSig w = op ∧
    w.treeRoot = rt ∧
    allZeroGoldilocks (forsOpeningResiduals geom pkSeed leafGlobalIdx t idx w) = true := by
  intro w
  simp only [verifySingleForsOpening.public_eqs] at hVer
  cases hChk : (decide (idx < 2 ^ geom.forsHeight) && (op.authPath.length == geom.forsHeight))
  · simp [hChk] at hVer
  · simp only [hChk, ↓reduceIte, Option.some.injEq] at hVer
    rcases Bool.and_eq_true_iff.mp hChk with ⟨hIdxDec, hMpLenB⟩
    have hMpLen : op.authPath.length = geom.forsHeight := eq_of_beq hMpLenB
    have hPermOut : (honestPoseidon2PermWitness ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩).output =
        poseidon2Perm12 ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩ := by
      unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
    let lp := honestPoseidon2PermWitness ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩
    let leaf := lane4Add lp.output.b0
      (poseidon2WeightedFeedForward
        ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩)
    have hLeafEq : leaf = forsLeafHash geom pkSeed op.secretVal leafGlobalIdx t idx := by
      dsimp only [leaf, lp]; rw [hPermOut, forsLeafHash_eq_perm]
    let mp := honestMerklePathWitness domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf op.authPath
    have hSibMap : mp.map MerkleLevelWitness.sibling = op.authPath :=
      map_sibOf_buildMerklePathWitnessPoly _ _ _ (fun _ _ _ _ => rfl) op.authPath 1 idx leaf
    have hMpWLen : mp.length = geom.forsHeight := by
      dsimp only [mp]; unfold honestMerklePathWitness
      rw [length_buildMerklePathWitnessPoly, hMpLen]
    have hMIff := merklePathResiduals_allZero_iff domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf mp
    have hMZero : allZeroGoldilocks (merklePathResiduals domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf mp).2 = true :=
      hMIff.1.mpr (by rw [hSibMap])
    have hWalkEq : (merklePathResiduals domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf mp).1 = rt := by
      rw [hMIff.2 (by rw [hSibMap]), hSibMap, hLeafEq, hVer]
    have hSigEq : forsOpeningWitnessSig w = op := by
      rcases op with ⟨sv, ap⟩
      unfold forsOpeningWitnessSig
      dsimp only [w, honestForsOpeningTraceWitness]
      simp only [AggForsTreeOpening.mk.injEq]
      exact ⟨trivial, hSibMap⟩
    refine ⟨hSigEq, hWalkEq, ?_⟩
    unfold forsOpeningResiduals
    dsimp only [w, honestForsOpeningTraceWitness]
    have hWChk : (decide (idx < 2 ^ geom.forsHeight) && (mp.length == geom.forsHeight)) = true := by
      rw [hIdxDec, hMpWLen]; simp
    simp only [allZeroGoldilocks_append, Bool.and_eq_true,
      permWithInputResiduals_allZero_iff, lane4Sub_toList_allZero_iff]
    exact ⟨⟨⟨shapeIte_allZero_of _ (Bool.and_eq_true_iff.mp hWChk), trivial⟩, hMZero⟩, trivial⟩

private def buildForsTracePoly {OP FW : Type}
    (mkF : Nat → Nat → OP → FW) :
    List Nat → List OP → Nat → List FW
  | [], _, _ => []
  | _, [], _ => []
  | idx :: idxs, op :: ops, t => mkF t idx op :: buildForsTracePoly mkF idxs ops (t + 1)

private def forsTraceResidualsPoly {FW RES : Type}
    (fRes : Nat → Nat → FW → List RES) (badRes : List RES) :
    List Nat → List FW → Nat → List RES
  | [], [], _ => []
  | idx :: idxs, w :: ws, t => fRes t idx w ++ forsTraceResidualsPoly fRes badRes idxs ws (t + 1)
  | [], _ :: _, _ => badRes
  | _ :: _, [], _ => badRes

private theorem forsTraceResidualsPoly_sound {D OP FW RES : Type}
    (fRes : Nat → Nat → FW → List RES)
    (vStep : Nat → Nat → OP → Option D)
    (sigOf : FW → OP)
    (rtOf : FW → D)
    (badRes : List RES)
    (zeroPred : List RES → Bool)
    (hBad : zeroPred badRes = false)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hStepSound : ∀ t idx w, zeroPred (fRes t idx w) = true → vStep t idx (sigOf w) = some (rtOf w)) :
    ∀ (idxs : List Nat) (ws : List FW) (t : Nat),
      zeroPred (forsTraceResidualsPoly fRes badRes idxs ws t) = true →
      idxs.length = ws.length ∧
      verifyForsPoly vStep idxs (ws.map sigOf) t = some (ws.map rtOf)
  | [], [], _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, hZ => by dsimp only [forsTraceResidualsPoly] at hZ; rw [hBad] at hZ; cases hZ
  | _ :: _, [], _, hZ => by dsimp only [forsTraceResidualsPoly] at hZ; rw [hBad] at hZ; cases hZ
  | idx :: idxs, w :: ws, t, hZ => by
    dsimp only [forsTraceResidualsPoly] at hZ ⊢
    rw [List.map_cons, List.map_cons]
    dsimp only [verifyForsPoly]
    rw [hAppend, Bool.and_eq_true] at hZ
    rw [hStepSound t idx w hZ.1]
    obtain ⟨hLen, hRest⟩ := forsTraceResidualsPoly_sound fRes vStep sigOf rtOf badRes zeroPred
      hBad hAppend hStepSound idxs ws (t + 1) hZ.2
    rw [hRest]
    exact ⟨congrArg Nat.succ hLen, rfl⟩

private theorem forsTraceResidualsPoly_complete {D OP FW RES : Type}
    (mkF : Nat → Nat → OP → FW)
    (fRes : Nat → Nat → FW → List RES)
    (vStep : Nat → Nat → OP → Option D)
    (sigOf : FW → OP)
    (rtOf : FW → D)
    (badRes : List RES)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hStepComplete : ∀ t idx op rt,
      vStep t idx op = some rt →
      sigOf (mkF t idx op) = op ∧
      rtOf (mkF t idx op) = rt ∧
      zeroPred (fRes t idx (mkF t idx op)) = true) :
    ∀ (idxs : List Nat) (ops : List OP) (t : Nat) (rts : List D),
      verifyForsPoly vStep idxs ops t = some rts →
      let ws := buildForsTracePoly mkF idxs ops t
      ws.map sigOf = ops ∧
      ws.map rtOf = rts ∧
      zeroPred (forsTraceResidualsPoly fRes badRes idxs ws t) = true
  | [], [], _, _, hVer => by
    dsimp only [verifyForsPoly, buildForsTracePoly, forsTraceResidualsPoly, List.map_nil] at hVer ⊢
    injection hVer with hEq
    exact ⟨rfl, hEq, hNil⟩
  | [], _ :: _, _, _, hVer => by dsimp only [verifyForsPoly] at hVer; cases hVer
  | _ :: _, [], _, _, hVer => by dsimp only [verifyForsPoly] at hVer; cases hVer
  | idx :: idxs, op :: ops, t, rts, hVer => by
    dsimp only [verifyForsPoly] at hVer
    cases hSt : vStep t idx op with
    | none => simp [hSt] at hVer
    | some rt0 =>
      simp only [hSt] at hVer
      cases hRest : verifyForsPoly vStep idxs ops (t + 1) with
      | none => simp [hRest] at hVer
      | some restRts =>
        simp only [hRest, Option.some.injEq] at hVer
        subst hVer
        obtain ⟨hS0, hR0, hZ0⟩ := hStepComplete t idx op rt0 hSt
        obtain ⟨ihS, ihR, ihZ⟩ := forsTraceResidualsPoly_complete mkF fRes vStep sigOf rtOf
          badRes zeroPred hNil hAppend hStepComplete idxs ops (t + 1) restRts hRest
        dsimp only [buildForsTracePoly, List.map_cons, forsTraceResidualsPoly]
        rw [hAppend, Bool.and_eq_true]
        exact ⟨List.cons_eq_cons.mpr ⟨hS0, ihS⟩, List.cons_eq_cons.mpr ⟨hR0, ihR⟩, ⟨hZ0, ihZ⟩⟩

/-- Full FORS multi-tree opening + `compressForsRootsSponge` sub-circuit witness. -/
structure ForsAndRecoverTraceWitness where
  openings    : List ForsOpeningTraceWitness
  rootsSponge : SpongeAbsorbWitness
  forsPkOut   : Digest4
  deriving DecidableEq, Repr

def honestForsAndRecoverTraceWitness (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (ops : List AggForsTreeOpening) : ForsAndRecoverTraceWitness :=
  let fws := buildForsTracePoly (honestForsOpeningTraceWitness geom pkSeed leafGlobalIdx) indices ops 0
  let rts := fws.map ForsOpeningTraceWitness.treeRoot
  let sp := honestSpongeAbsorbWitness (forsRootsInitState geom pkSeed leafGlobalIdx) rts
  { openings := fws, rootsSponge := sp, forsPkOut := sp.outDigest }

def forsAndRecoverTraceResiduals (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (w : ForsAndRecoverTraceWitness) : List Goldilocks :=
  let shapeRes :=
    if indices.length == geom.forsTrees && w.openings.length == geom.forsTrees then []
    else [Goldilocks.one]
  let rts := w.openings.map ForsOpeningTraceWitness.treeRoot
  shapeRes ++
  forsTraceResidualsPoly (forsOpeningResiduals geom pkSeed leafGlobalIdx) [Goldilocks.one] indices w.openings 0 ++
  spongeAbsorbResiduals (forsRootsInitState geom pkSeed leafGlobalIdx) rts w.rootsSponge ++
  (lane4Sub w.forsPkOut w.rootsSponge.outDigest).toList

theorem forsAndRecoverTraceResiduals_sound (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (w : ForsAndRecoverTraceWitness)
    (hZero : allZeroGoldilocks (forsAndRecoverTraceResiduals geom pkSeed leafGlobalIdx indices w) = true) :
    verifyAndRecoverForsPk geom pkSeed leafGlobalIdx indices (w.openings.map forsOpeningWitnessSig) =
      some w.forsPkOut := by
  unfold forsAndRecoverTraceResiduals at hZero
  dsimp only at hZero
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff] at hZero
  rcases hZero with ⟨⟨⟨hShape, hF⟩, hSp⟩, hOutEq⟩
  have hLenChk := shapeIte_allZero _ hShape
  · obtain ⟨_, hVerF⟩ := forsTraceResidualsPoly_sound
      (forsOpeningResiduals geom pkSeed leafGlobalIdx)
      (verifySingleForsOpening geom pkSeed leafGlobalIdx)
      forsOpeningWitnessSig ForsOpeningTraceWitness.treeRoot
      [Goldilocks.one] allZeroGoldilocks (by decide) allZeroGoldilocks_append
      (forsOpeningResiduals_sound geom pkSeed leafGlobalIdx) indices w.openings 0 hF
    have hSpIff := forsRootsSpongeResiduals_allZero_iff geom pkSeed leafGlobalIdx
      (w.openings.map ForsOpeningTraceWitness.treeRoot) w.rootsSponge
    have hSpOut := hSpIff.2 (hSpIff.1.mp hSp)
    simp only [verifyAndRecoverForsPk.public_eqs, verifyForsTreesAux.public_eqs]
    have hMapLen :
        (indices.length == geom.forsTrees && (w.openings.map forsOpeningWitnessSig).length == geom.forsTrees) = true := by
      rw [List.length_map, Bool.and_eq_true]; exact hLenChk
    simp only [hMapLen, ↓reduceIte, hVerF, Option.some.injEq]
    rw [hOutEq, hSpOut]

theorem forsAndRecoverTraceResiduals_complete (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (ops : List AggForsTreeOpening) (fpk : Digest4)
    (hVer : verifyAndRecoverForsPk geom pkSeed leafGlobalIdx indices ops = some fpk) :
    let w := honestForsAndRecoverTraceWitness geom pkSeed leafGlobalIdx indices ops
    w.openings.map forsOpeningWitnessSig = ops ∧
    w.forsPkOut = fpk ∧
    allZeroGoldilocks (forsAndRecoverTraceResiduals geom pkSeed leafGlobalIdx indices w) = true := by
  intro w
  simp only [verifyAndRecoverForsPk.public_eqs, verifyForsTreesAux.public_eqs] at hVer
  cases hLenChk : (indices.length == geom.forsTrees && ops.length == geom.forsTrees)
  · simp [hLenChk] at hVer
  · simp only [hLenChk, ↓reduceIte] at hVer
    cases hFT : verifyForsPoly (verifySingleForsOpening geom pkSeed leafGlobalIdx) indices ops 0 with
    | none => simp [hFT] at hVer
    | some rts =>
      simp only [hFT, Option.some.injEq] at hVer
      obtain ⟨hMapS, hMapR, hFZ⟩ := forsTraceResidualsPoly_complete
        (honestForsOpeningTraceWitness geom pkSeed leafGlobalIdx)
        (forsOpeningResiduals geom pkSeed leafGlobalIdx)
        (verifySingleForsOpening geom pkSeed leafGlobalIdx)
        forsOpeningWitnessSig ForsOpeningTraceWitness.treeRoot
        [Goldilocks.one] allZeroGoldilocks rfl allZeroGoldilocks_append
        (forsOpeningResiduals_complete geom pkSeed leafGlobalIdx) indices ops 0 rts hFT
      let fws := buildForsTracePoly (honestForsOpeningTraceWitness geom pkSeed leafGlobalIdx) indices ops 0
      have hFwsLen : fws.length = ops.length := by
        have h1 : (fws.map forsOpeningWitnessSig).length = ops.length := by rw [hMapS]
        simpa only [List.length_map] using h1
      let rtsW := fws.map ForsOpeningTraceWitness.treeRoot
      let sp := honestSpongeAbsorbWitness (forsRootsInitState geom pkSeed leafGlobalIdx) rtsW
      have hSpIff := forsRootsSpongeResiduals_allZero_iff geom pkSeed leafGlobalIdx rtsW sp
      have hSpZ : allZeroGoldilocks (spongeAbsorbResiduals
          (forsRootsInitState geom pkSeed leafGlobalIdx) rtsW sp) = true := hSpIff.1.mpr rfl
      have hSpOut : sp.outDigest = fpk := by
        rw [hSpIff.2 rfl]
        have hRtsEq : rtsW = rts := hMapR
        rw [hRtsEq, hVer]
      refine ⟨hMapS, hSpOut, ?_⟩
      unfold forsAndRecoverTraceResiduals
      dsimp only [w, honestForsAndRecoverTraceWitness]
      have hWLenChk : (indices.length == geom.forsTrees && fws.length == geom.forsTrees) = true := by
        rw [hFwsLen]; exact hLenChk
      simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff]
      exact ⟨⟨⟨shapeIte_allZero_of _ (Bool.and_eq_true_iff.mp hWLenChk), hFZ⟩, hSpZ⟩, trivial⟩

/-- 2-block stateless XOF + 7-limb `< 2^63` quartic/MSB algebraic witness (`sig.rs:494`). -/
structure StatelessXofTraceWitness where
  perm0 : Poseidon2PermWitness
  perm1 : Poseidon2PermWitness
  lim0  : Limb63DecompWitness
  lim1  : Limb63DecompWitness
  lim2  : Limb63DecompWitness
  lim3  : Limb63DecompWitness
  lim4  : Limb63DecompWitness
  lim5  : Limb63DecompWitness
  lim6  : Limb63DecompWitness
  deriving DecidableEq, Repr

private def statelessXofIn0 (pk : AggValidatorPk) (mu : Digest5) : Poseidon2State12 :=
  ⟨pk.pkSeed, pk.pkRoot, ⟨domainHMsgStateless, mu.limb4, Goldilocks.zero, poseidon2IvTag⟩⟩

private def statelessXofIn1 (st0 : Poseidon2State12) (rRand : Digest4) (mu : Digest5) : Poseidon2State12 :=
  let muLow : Digest4 := ⟨mu.limb0, mu.limb1, mu.limb2, mu.limb3⟩
  ⟨lane4Add st0.b0 rRand, lane4Add st0.b1 muLow, st0.b2⟩

private theorem statelessXofSpongeState_eq_states (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5) :
    statelessXofSpongeState pk rRand mu =
      poseidon2Perm12 (statelessXofIn1 (poseidon2Perm12 (statelessXofIn0 pk mu)) rRand mu) := by
  simp only [statelessXofSpongeState.public_eqs]
  unfold statelessXofIn0 statelessXofIn1
  rfl

attribute [local irreducible] statelessXofIn0 statelessXofIn1

def honestStatelessXofTraceWitness (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5) :
    StatelessXofTraceWitness :=
  let p0 := honestPoseidon2PermWitness (statelessXofIn0 pk mu)
  let p1 := honestPoseidon2PermWitness (statelessXofIn1 p0.output rRand mu)
  let st := p1.output
  { perm0 := p0, perm1 := p1
    lim0 := honestLimb63DecompWitness st.b0.x0
    lim1 := honestLimb63DecompWitness st.b0.x1
    lim2 := honestLimb63DecompWitness st.b0.x2
    lim3 := honestLimb63DecompWitness st.b0.x3
    lim4 := honestLimb63DecompWitness st.b1.x0
    lim5 := honestLimb63DecompWitness st.b1.x1
    lim6 := honestLimb63DecompWitness st.b1.x2 }

def extractStatelessXofPair (geom : AggSigGeometry) (w : StatelessXofTraceWitness) : (Nat × List Nat) :=
  let st1 := w.perm1.output
  let totalTreeBits := geom.numLayers * geom.subtreeHeight
  let rawLeaf := (st1.b1.x1.val % (2 ^ 32)) + ((st1.b1.x2.val % (2 ^ 32)) * (2 ^ 32))
  let leafGlobalIdx := rawLeaf % (2 ^ totalTreeBits)
  let treeMod := 2 ^ geom.forsHeight
  let indices := (List.range geom.forsTrees).map fun t =>
    let limbVal := match t / 7 with
      | 0 => st1.b0.x0.val
      | 1 => st1.b0.x1.val
      | 2 => st1.b0.x2.val
      | 3 => st1.b0.x3.val
      | _ => st1.b1.x0.val
    (limbVal / (256 ^ (t % 7))) % treeMod
  (leafGlobalIdx, indices)

def statelessXofTraceResiduals (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5)
    (w : StatelessXofTraceWitness) : List Goldilocks :=
  let st := w.perm1.output
  permWithInputResiduals (statelessXofIn0 pk mu) w.perm0 ++
  permWithInputResiduals (statelessXofIn1 w.perm0.output rRand mu) w.perm1 ++
  limb63DecompResiduals st.b0.x0 w.lim0 ++
  limb63DecompResiduals st.b0.x1 w.lim1 ++
  limb63DecompResiduals st.b0.x2 w.lim2 ++
  limb63DecompResiduals st.b0.x3 w.lim3 ++
  limb63DecompResiduals st.b1.x0 w.lim4 ++
  limb63DecompResiduals st.b1.x1 w.lim5 ++
  limb63DecompResiduals st.b1.x2 w.lim6

theorem statelessXofTraceResiduals_sound (geom : AggSigGeometry) (pk : AggValidatorPk)
    (rRand : Digest4) (mu : Digest5) (w : StatelessXofTraceWitness)
    (hZero : allZeroGoldilocks (statelessXofTraceResiduals pk rRand mu w) = true) :
    deriveStatelessLeafAndForsChecked geom pk rRand mu = some (extractStatelessXofPair geom w) := by
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  unfold statelessXofTraceResiduals at hZero
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, permWithInputResiduals_allZero_iff,
    limb63DecompResiduals_allZero_iff] at hZero
  rcases hZero with ⟨⟨⟨⟨⟨⟨⟨⟨hP0, hP1⟩, ⟨c0, _⟩⟩, ⟨c1, _⟩⟩, ⟨c2, _⟩⟩, ⟨c3, _⟩⟩, ⟨c4, _⟩⟩, ⟨c5, _⟩⟩, ⟨c6, _⟩⟩
  have hStEq : w.perm1.output = statelessXofSpongeState pk rRand mu := by
    rw [hP1, hP0, hPermOut, hPermOut, statelessXofSpongeState_eq_states]
  simp only [deriveStatelessLeafAndForsChecked.public_eqs]
  unfold extractStatelessXofPair
  rw [← hStEq]
  have hAll63 :
      ([w.perm1.output.b0.x0, w.perm1.output.b0.x1, w.perm1.output.b0.x2, w.perm1.output.b0.x3,
        w.perm1.output.b1.x0, w.perm1.output.b1.x1, w.perm1.output.b1.x2].all
        (fun l => decide (l.val < 2 ^ 63))) = true := by
    simp [c0, c1, c2, c3, c4, c5, c6]
  simp only [hAll63, ↓reduceIte]
  rfl

theorem statelessXofTraceResiduals_complete (geom : AggSigGeometry) (pk : AggValidatorPk)
    (rRand : Digest4) (mu : Digest5) (leafIdx : Nat) (indices : List Nat)
    (hXof : deriveStatelessLeafAndForsChecked geom pk rRand mu = some (leafIdx, indices)) :
    let w := honestStatelessXofTraceWitness pk rRand mu
    extractStatelessXofPair geom w = (leafIdx, indices) ∧
    allZeroGoldilocks (statelessXofTraceResiduals pk rRand mu w) = true := by
  intro w
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  have hStEq : w.perm1.output = statelessXofSpongeState pk rRand mu := by
    dsimp only [w, honestStatelessXofTraceWitness]
    rw [hPermOut, hPermOut, statelessXofSpongeState_eq_states]
  simp only [deriveStatelessLeafAndForsChecked.public_eqs] at hXof
  rw [← hStEq] at hXof
  cases hAll63 : ([w.perm1.output.b0.x0, w.perm1.output.b0.x1, w.perm1.output.b0.x2, w.perm1.output.b0.x3,
                   w.perm1.output.b1.x0, w.perm1.output.b1.x1, w.perm1.output.b1.x2].all
                   (fun l => decide (l.val < 2 ^ 63)))
  · simp [hAll63] at hXof
  · simp only [hAll63, ↓reduceIte, Option.some.injEq] at hXof
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hAll63
    rcases hAll63 with ⟨c0, c1, c2, c3, c4, c5, c6⟩
    refine ⟨hXof, ?_⟩
    unfold statelessXofTraceResiduals
    dsimp only [w, honestStatelessXofTraceWitness]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, permWithInputResiduals_allZero_iff,
      limb63DecompResiduals_allZero_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨trivial, trivial⟩, ⟨c0, trivial⟩⟩, ⟨c1, trivial⟩⟩, ⟨c2, trivial⟩⟩, ⟨c3, trivial⟩⟩, ⟨c4, trivial⟩⟩, ⟨c5, trivial⟩⟩, ⟨c6, trivial⟩⟩


/-! ### Full `AggSignerTraceWitness`, `RowGate7` AST, `AggExecutionTrace`, & AIR Constraint Exactness -/

/-- Non-zero field encoding of `AggSigProfile` (`1` for `XmssPoseidon2`, `2` for `CorduroyPoseidon2`). -/
def profileFieldTag : AggSigProfile → Goldilocks
  | .xmssPoseidon2 => Goldilocks.one
  | .corduroyPoseidon2  => Goldilocks.ofNat 2

theorem profileFieldTag_ne_zero (p : AggSigProfile) : profileFieldTag p ≠ Goldilocks.zero := by
  cases p <;> decide

theorem profileFieldTag_injective {p1 p2 : AggSigProfile}
    (h : profileFieldTag p1 = profileFieldTag p2) : p1 = p2 := by
  cases p1 <;> cases p2 <;> first | rfl | (exfalso; revert h; decide)

inductive AggSignerModeTrace where
  | stateful (leafIdx : Nat) (hmsg0 : HmsgStatefulTraceWitness)
  | stateless (xof : StatelessXofTraceWitness)
              (fors : ForsAndRecoverTraceWitness)
              (hmsg0 : HmsgDetTreeTraceWitness)
  deriving DecidableEq, Repr

structure AggSignerTraceWitness where
  profile    : AggSigProfile
  rRand      : Digest4
  modeTrace  : AggSignerModeTrace
  layer0     : WotsLayerTraceWitness
  upperNodes : List UpperLayerTraceNode
  deriving DecidableEq, Repr

def extractSignerWitnessSig (w : AggSignerTraceWitness) : AggNativeSignature :=
  let (leafIdx, forsOps) := match w.modeTrace with
    | .stateful idx _ => (idx, [])
    | .stateless _ fors _ => (0, fors.openings.map forsOpeningWitnessSig)
  { profile         := w.profile
    rRand           := w.rRand
    statefulLeafIdx := leafIdx
    forsOpenings    := forsOps
    layers          := wotsLayerWitnessSig w.layer0 ::
                       w.upperNodes.map (fun nw => wotsLayerWitnessSig nw.wotsStep) }

def signerTraceResiduals (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8)
    (w : AggSignerTraceWitness) : List Goldilocks :=
  let hdrOk := geom.wellFormed && (pk.profile == geom.profile) &&
               (w.profile == geom.profile) && (w.upperNodes.length + 1 == geom.numLayers)
  let hdrRes := if hdrOk then [] else [Goldilocks.one]
  let mu := computeMessageMu pk msg
  let bodyRes := match w.modeTrace with
    | .stateful leafIdx hmsgW =>
      let modeOk := (geom.forsTrees == 0) && decide (leafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))
      let modeRes := if modeOk then [] else [Goldilocks.one]
      let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
      let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
      let (topRt, upRes) := upperLayersTraceResiduals geom pk 1 tr0 w.layer0.rootOut w.upperNodes
      modeRes ++
      hmsgStatefulResiduals pk w.rRand mu kp0 w.layer0.tswCtr hmsgW ++
      wotsLayerTraceResiduals geom pk 0 tr0 kp0 hmsgW.outMsg w.layer0 ++
      upRes ++
      (lane4Sub topRt pk.pkRoot).toList
    | .stateless xofW forsW hmsgW =>
      let modeOk := !(geom.forsTrees == 0)
      let modeRes := if modeOk then [] else [Goldilocks.one]
      let (leafIdx, forsIndices) := extractStatelessXofPair geom xofW
      let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
      let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
      let (topRt, upRes) := upperLayersTraceResiduals geom pk 1 tr0 w.layer0.rootOut w.upperNodes
      modeRes ++
      statelessXofTraceResiduals pk w.rRand mu xofW ++
      forsAndRecoverTraceResiduals geom pk.pkSeed leafIdx forsIndices forsW ++
      hmsgDetTreeResiduals pk 0 tr0 kp0 w.layer0.tswCtr forsW.forsPkOut hmsgW ++
      wotsLayerTraceResiduals geom pk 0 tr0 kp0 hmsgW.outMsg w.layer0 ++
      upRes ++
      (lane4Sub topRt pk.pkRoot).toList
  hdrRes ++ bodyRes

private theorem wellFormed_unpack_wots (geom : AggSigGeometry) (hWf : geom.wellFormed = true) :
    geom.wotsChains ≤ 128 ∧ geom.targetSum < 3 * geom.wotsChains := by
  unfold AggSigGeometry.wellFormed at hWf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
  exact ⟨hWf.1.1.1.1.1.1.2, hWf.1.1.1.1.2⟩

theorem signerTraceResiduals_sound (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8)
    (w : AggSignerTraceWitness)
    (hZero : allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true) :
    verifyAggNativeSig geom pk msg (extractSignerWitnessSig w) = true := by
  unfold signerTraceResiduals at hZero
  dsimp only at hZero
  rw [allZeroGoldilocks_append, Bool.and_eq_true] at hZero
  rcases hZero with ⟨hHdr, hBody⟩
  cases hHdrB : (geom.wellFormed && (pk.profile == geom.profile) &&
                 (w.profile == geom.profile) && (w.upperNodes.length + 1 == geom.numLayers))
  · rw [hHdrB] at hHdr; exact absurd hHdr (by decide)
  · simp only [Bool.and_eq_true] at hHdrB
    rcases hHdrB with ⟨⟨⟨hWf, hPkProfB⟩, hWProfB⟩, hLenB⟩
    have hPkProf : pk.profile = geom.profile := eq_of_beq hPkProfB
    have hWProf : w.profile = geom.profile := eq_of_beq hWProfB
    have hUpperLen : w.upperNodes.length + 1 = geom.numLayers := eq_of_beq hLenB
    obtain ⟨hChainsLe, hTargetBound⟩ := wellFormed_unpack_wots geom hWf
    cases hMode : w.modeTrace with
    | stateful leafIdx hmsgW =>
      rw [hMode] at hBody
      dsimp only at hBody
      cases hMCond : ((geom.forsTrees == 0) && decide (leafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight)))
      · rw [hMCond] at hBody
        simp only [allZeroGoldilocks_append, Bool.and_eq_true] at hBody
        exact absurd hBody.1.1.1.1 (by decide)
      · rw [hMCond] at hBody
        simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff] at hBody
        rcases hBody with ⟨⟨⟨⟨-, hHm⟩, hW0⟩, hUp⟩, hTopEq⟩
        rcases Bool.and_eq_true_iff.mp hMCond with ⟨hFors0, hLeafDec⟩
        have hLeafLt : leafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight) := of_decide_eq_true hLeafDec
        let mu := computeMessageMu pk msg
        let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
        let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
        have hHmIff := hmsgStatefulResiduals_allZero_iff pk w.rRand mu kp0 w.layer0.tswCtr hmsgW
        have hHmOut : hmsgW.outMsg = computeHmsgStateful pk w.rRand mu kp0 w.layer0.tswCtr :=
          hHmIff.2 (hHmIff.1.mp hHm)
        have hVer0 := wotsLayerTraceResiduals_sound geom pk 0 tr0 kp0 hmsgW.outMsg w.layer0
          hChainsLe hTargetBound hW0
        rw [hHmOut] at hVer0
        have hVerUp := upperLayersTraceResiduals_sound geom pk 1 tr0 w.layer0.rootOut w.upperNodes
          hChainsLe hTargetBound hUp
        rw [hTopEq] at hVerUp
        unfold extractSignerWitnessSig
        rw [hMode, hWProf]
        dsimp only
        refine verifyAggNativeSig_stateful_of_ok geom pk msg w.rRand leafIdx
          (wotsLayerWitnessSig w.layer0)
          (w.upperNodes.map fun nw => wotsLayerWitnessSig nw.wotsStep)
          w.layer0.rootOut hWf hPkProf ?_ hFors0 hLeafLt hVer0 hVerUp
        simpa only [List.length_map] using hUpperLen
    | stateless xofW forsW hmsgW =>
      rw [hMode] at hBody
      dsimp only at hBody
      simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff] at hBody
      rcases hBody with ⟨⟨⟨⟨⟨⟨hModeOk, hXofZ⟩, hForsZ⟩, hHmZ⟩, hW0Z⟩, hUpZ⟩, hTopEq⟩
      cases hMCond : (!(geom.forsTrees == 0))
      · rw [hMCond] at hModeOk; exact absurd hModeOk (by decide)
      · have hFors0 : (geom.forsTrees == 0) = false := (Bool.not_eq_true' _).mp hMCond
        let mu := computeMessageMu pk msg
        have hXofOk := statelessXofTraceResiduals_sound geom pk w.rRand mu xofW hXofZ
        let pair := extractStatelessXofPair geom xofW
        have hForsOk := forsAndRecoverTraceResiduals_sound geom pk.pkSeed pair.1 pair.2 forsW hForsZ
        let kp0 := pair.1 % (2 ^ geom.subtreeHeight)
        let tr0 := pair.1 / (2 ^ geom.subtreeHeight)
        have hHmIff := hmsgDetTreeResiduals_allZero_iff pk 0 tr0 kp0 w.layer0.tswCtr forsW.forsPkOut hmsgW
        have hHmOut : hmsgW.outMsg = computeHmsgDetTree pk 0 tr0 kp0 w.layer0.tswCtr forsW.forsPkOut :=
          hHmIff.2 (hHmIff.1.mp hHmZ)
        have hVer0 := wotsLayerTraceResiduals_sound geom pk 0 tr0 kp0 hmsgW.outMsg w.layer0
          hChainsLe hTargetBound hW0Z
        rw [hHmOut] at hVer0
        have hVerUp := upperLayersTraceResiduals_sound geom pk 1 tr0 w.layer0.rootOut w.upperNodes
          hChainsLe hTargetBound hUpZ
        rw [hTopEq] at hVerUp
        unfold extractSignerWitnessSig
        rw [hMode, hWProf]
        dsimp only
        refine verifyAggNativeSig_stateless_of_ok geom pk msg w.rRand
          (forsW.openings.map forsOpeningWitnessSig)
          (wotsLayerWitnessSig w.layer0)
          (w.upperNodes.map fun nw => wotsLayerWitnessSig nw.wotsStep)
          pair.1 pair.2 forsW.forsPkOut w.layer0.rootOut
          hWf hPkProf ?_ hFors0 ?_ hForsOk hVer0 hVerUp
        · simpa only [List.length_map] using hUpperLen
        · exact hXofOk

def buildHonestSignerTraceWitness (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8)
    (sig : AggNativeSignature) : AggSignerTraceWitness :=
  let mu := computeMessageMu pk msg
  let lsig0 := sig.layers.headD { tswCtr := 0, wotsChains := [], merklePath := [] }
  let upperLs := sig.layers.tail
  if geom.forsTrees == 0 then
    let kp0 := sig.statefulLeafIdx % (2 ^ geom.subtreeHeight)
    let tr0 := sig.statefulLeafIdx / (2 ^ geom.subtreeHeight)
    let hmW := honestHmsgStatefulTraceWitness pk sig.rRand mu kp0 lsig0.tswCtr
    let w0 := honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0
    let upW := honestUpperLayersTrace geom pk 1 tr0 w0.rootOut upperLs
    { profile := sig.profile, rRand := sig.rRand,
      modeTrace := .stateful sig.statefulLeafIdx hmW,
      layer0 := w0, upperNodes := upW }
  else
    let xofW := honestStatelessXofTraceWitness pk sig.rRand mu
    let (leafIdx, forsIndices) := extractStatelessXofPair geom xofW
    let forsW := honestForsAndRecoverTraceWitness geom pk.pkSeed leafIdx forsIndices sig.forsOpenings
    let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
    let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
    let hmW := honestHmsgDetTreeTraceWitness pk 0 tr0 kp0 lsig0.tswCtr forsW.forsPkOut
    let w0 := honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0
    let upW := honestUpperLayersTrace geom pk 1 tr0 w0.rootOut upperLs
    { profile := sig.profile, rRand := sig.rRand,
      modeTrace := .stateless xofW forsW hmW,
      layer0 := w0, upperNodes := upW }

private theorem allZeroGoldilocks_append_intro {a b : List Goldilocks}
    (ha : allZeroGoldilocks a = true) (hb : allZeroGoldilocks b = true) :
    allZeroGoldilocks (a ++ b) = true := by
  rw [allZeroGoldilocks_append, ha, hb]
  rfl

theorem signerTraceResiduals_complete (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8)
    (sig : AggNativeSignature)
    (hVer : verifyAggNativeSig geom pk msg sig = true) :
    let w := buildHonestSignerTraceWitness geom pk msg sig
    extractSignerWitnessSig w = sig ∧
    allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true := by
  intro w
  unfold verifyAggNativeSig at hVer
  rcases Bool.eq_false_or_eq_true (!geom.wellFormed || pk.profile != geom.profile ||
      sig.profile != geom.profile || sig.layers.length != geom.numLayers) with hHdr | hHdr
  · simp only [hHdr, ↓reduceIte] at hVer
    cases hVer
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte] at hVer
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', bne_eq_false_iff_eq] at hHdr
    rcases hHdr with ⟨⟨⟨hWf, hPkProf⟩, hSigProf⟩, hLayLen⟩
    obtain ⟨hChainsLe, hTargetBound⟩ := wellFormed_unpack_wots geom hWf
    cases hLayers : sig.layers with
    | nil => rw [hLayers] at hVer; cases hVer
    | cons lsig0 upperLs =>
      rw [hLayers] at hVer
      dsimp only at hVer
      have hUpperLen : upperLs.length + 1 = geom.numLayers := by
        rw [← hLayLen, hLayers]; simp
      let mu := computeMessageMu pk msg
      cases hFors0 : (geom.forsTrees == 0)
      · -- Stateless
        rw [hFors0] at hVer
        simp only [Bool.false_eq_true, ↓reduceIte] at hVer
        delta verifyAggNativeSigStateless at hVer
        rcases unpackStatelessFlow hVer with
          ⟨leafIdx, forsIndices, forsPk, root0, topRoot, hLeafNz, hXof, hForsVer, hW0, hUp, hTopBeq⟩
        have hLeafZ : sig.statefulLeafIdx = 0 := bne_eq_false_iff_eq.mp hLeafNz
        have hTopEq : topRoot = pk.pkRoot := eq_of_beq hTopBeq
        obtain ⟨hXofPair, hXofZ⟩ := statelessXofTraceResiduals_complete geom pk sig.rRand mu leafIdx forsIndices hXof
        obtain ⟨hForsMap, hForsOut, hForsZ⟩ := forsAndRecoverTraceResiduals_complete geom pk.pkSeed
          leafIdx forsIndices sig.forsOpenings forsPk hForsVer
        let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
        let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
        let hmW := honestHmsgDetTreeTraceWitness pk 0 tr0 kp0 lsig0.tswCtr forsPk
        have hHmIff := hmsgDetTreeResiduals_allZero_iff pk 0 tr0 kp0 lsig0.tswCtr forsPk hmW
        have hHmOut : hmW.outMsg = computeHmsgDetTree pk 0 tr0 kp0 lsig0.tswCtr forsPk := hHmIff.2 rfl
        have hHmZ : allZeroGoldilocks (hmsgDetTreeResiduals pk 0 tr0 kp0 lsig0.tswCtr forsPk hmW) = true :=
          hHmIff.1.mpr rfl
        have hW0Sub : verifyWotsLayer geom pk 0 tr0 kp0 hmW.outMsg lsig0 = some root0 := by
          rw [hHmOut]; exact hW0
        obtain ⟨hW0Sig, hW0Rt, hW0Z⟩ := wotsLayerTraceResiduals_complete geom pk 0 tr0 kp0
          hmW.outMsg lsig0 root0 hChainsLe hTargetBound hW0Sub
        have hUpSub : verifyUpperLayers geom pk 1 tr0
            (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs = some topRoot := by
          rw [hW0Rt]; exact hUp
        obtain ⟨hUpMap, hUpTop, hUpZ⟩ := upperLayersTraceResiduals_complete geom pk 1 tr0
          _ topRoot upperLs hChainsLe hTargetBound hUpSub
        have hUpWLen : (honestUpperLayersTrace geom pk 1 tr0
            (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).length + 1 =
            geom.numLayers := by
          have h1 : ((honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).map
              (fun nw => wotsLayerWitnessSig nw.wotsStep)).length = upperLs.length := by rw [hUpMap]
          rw [List.length_map] at h1
          omega
        have hWDef : w = {
            profile := sig.profile, rRand := sig.rRand,
            modeTrace := .stateless (honestStatelessXofTraceWitness pk sig.rRand mu)
                           (honestForsAndRecoverTraceWitness geom pk.pkSeed leafIdx forsIndices sig.forsOpenings) hmW,
            layer0 := honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0,
            upperNodes := honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs } := by
          dsimp only [w, buildHonestSignerTraceWitness]
          simp only [hLayers, List.headD_cons, List.tail_cons, hFors0, Bool.false_eq_true, ↓reduceIte]
          rw [hXofPair]
          dsimp only
          rw [hForsOut]
        rw [hWDef]
        refine ⟨?_, ?_⟩
        · rcases sig with ⟨pr, rr, sli, fops, lays⟩
          dsimp only at hLeafZ hLayers hForsMap hW0Sig hUpMap ⊢
          subst hLeafZ hLayers
          unfold extractSignerWitnessSig
          dsimp only
          simp only [AggNativeSignature.mk.injEq, List.cons.injEq]
          exact ⟨trivial, trivial, trivial, hForsMap, hW0Sig, hUpMap⟩
        · unfold signerTraceResiduals
          dsimp only
          have hHdrTrue :
              (geom.wellFormed && (pk.profile == geom.profile) &&
               (sig.profile == geom.profile) &&
               ((honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).length + 1 == geom.numLayers)) = true := by
            rw [hWf, hPkProf, hSigProf, hUpWLen]
            simp only [beq_self_eq_true, Bool.and_self]
          rw [hHdrTrue, hFors0, hXofPair, hForsOut]
          have hNil : allZeroGoldilocks (if true = true then [] else [Goldilocks.one]) = true := by decide
          have hNil' : allZeroGoldilocks (if (!false) = true then [] else [Goldilocks.one]) = true := by decide
          have hCtr0 : (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).tswCtr = lsig0.tswCtr := rfl
          refine allZeroGoldilocks_append_intro hNil
            (allZeroGoldilocks_append_intro
              (allZeroGoldilocks_append_intro
                (allZeroGoldilocks_append_intro
                  (allZeroGoldilocks_append_intro
                    (allZeroGoldilocks_append_intro
                      (allZeroGoldilocks_append_intro hNil' hXofZ) hForsZ) ?_) hW0Z) hUpZ)
              ((lane4Sub_toList_allZero_iff _ _).mpr (hUpTop.trans hTopEq)))
          rw [hCtr0]
          exact hHmZ
      · -- Stateful
        rw [hFors0] at hVer
        simp only [↓reduceIte] at hVer
        unfold verifyAggNativeSigStateful at hVer
        rcases Bool.eq_false_or_eq_true (!sig.forsOpenings.isEmpty ||
            !(decide (sig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight)))) with hSChk | hSChk
        · simp only [hSChk, ↓reduceIte] at hVer
          cases hVer
        · simp only [hSChk, Bool.false_eq_true, ↓reduceIte] at hVer
          simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff, decide_eq_true_eq] at hSChk
          rcases hSChk with ⟨hForsNil, hLeafLt⟩
          let kp0 := sig.statefulLeafIdx % (2 ^ geom.subtreeHeight)
          let tr0 := sig.statefulLeafIdx / (2 ^ geom.subtreeHeight)
          let hmsg0 := computeHmsgStateful pk sig.rRand mu kp0 lsig0.tswCtr
          change (match verifyWotsLayer geom pk 0 tr0 kp0 hmsg0 lsig0 with
                  | none => false
                  | some root0 =>
                    match verifyUpperLayers geom pk 1 tr0 root0 upperLs with
                    | none => false
                    | some topRoot => topRoot == pk.pkRoot) = true at hVer
          cases hW0 : verifyWotsLayer geom pk 0 tr0 kp0 hmsg0 lsig0 with
          | none => rw [hW0] at hVer; cases hVer
          | some root0 =>
            rw [hW0] at hVer; dsimp only at hVer
            cases hUp : verifyUpperLayers geom pk 1 tr0 root0 upperLs with
            | none => rw [hUp] at hVer; cases hVer
            | some topRoot =>
              rw [hUp] at hVer; dsimp only at hVer
              have hTopEq : topRoot = pk.pkRoot := eq_of_beq hVer
              let hmW := honestHmsgStatefulTraceWitness pk sig.rRand mu kp0 lsig0.tswCtr
              have hHmIff := hmsgStatefulResiduals_allZero_iff pk sig.rRand mu kp0 lsig0.tswCtr hmW
              have hHmOut : hmW.outMsg = hmsg0 := hHmIff.2 rfl
              have hHmZ : allZeroGoldilocks (hmsgStatefulResiduals pk sig.rRand mu kp0 lsig0.tswCtr hmW) = true :=
                hHmIff.1.mpr rfl
              have hW0Sub : verifyWotsLayer geom pk 0 tr0 kp0 hmW.outMsg lsig0 = some root0 := by
                rw [hHmOut]; exact hW0
              obtain ⟨hW0Sig, hW0Rt, hW0Z⟩ := wotsLayerTraceResiduals_complete geom pk 0 tr0 kp0
                hmW.outMsg lsig0 root0 hChainsLe hTargetBound hW0Sub
              have hUpSub : verifyUpperLayers geom pk 1 tr0
                  (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs = some topRoot := by
                rw [hW0Rt]; exact hUp
              obtain ⟨hUpMap, hUpTop, hUpZ⟩ := upperLayersTraceResiduals_complete geom pk 1 tr0
                _ topRoot upperLs hChainsLe hTargetBound hUpSub
              have hUpWLen : (honestUpperLayersTrace geom pk 1 tr0
                  (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).length + 1 =
                  geom.numLayers := by
                have h1 : ((honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).map
                    (fun nw => wotsLayerWitnessSig nw.wotsStep)).length = upperLs.length := by rw [hUpMap]
                rw [List.length_map] at h1
                omega
              have hWDef : w = {
                  profile := sig.profile, rRand := sig.rRand,
                  modeTrace := .stateful sig.statefulLeafIdx hmW,
                  layer0 := honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0,
                  upperNodes := honestUpperLayersTrace geom pk 1 tr0
                    (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs } := by
                dsimp only [w, buildHonestSignerTraceWitness]
                simp only [hLayers, List.headD_cons, List.tail_cons, hFors0, ↓reduceIte, hmW, tr0, kp0, mu]
              rw [hWDef]
              refine ⟨?_, ?_⟩
              · rcases sig with ⟨pr, rr, sli, fops, lays⟩
                dsimp only at hForsNil hLayers hW0Sig hUpMap ⊢
                subst hForsNil hLayers
                unfold extractSignerWitnessSig
                dsimp only
                simp only [AggNativeSignature.mk.injEq, List.cons.injEq]
                exact ⟨trivial, trivial, trivial, trivial, hW0Sig, hUpMap⟩
              · unfold signerTraceResiduals
                dsimp only
                have hHdrTrue :
                    (geom.wellFormed && (pk.profile == geom.profile) &&
                     (sig.profile == geom.profile) &&
                     ((honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).length + 1 == geom.numLayers)) = true := by
                  rw [hWf, hPkProf, hSigProf, hUpWLen]
                  simp only [beq_self_eq_true, Bool.and_self]
                have hModeTrue :
                    ((geom.forsTrees == 0) && decide (sig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))) = true := by
                  rw [hFors0, decide_eq_true hLeafLt]
                  rfl
                rw [hHdrTrue, hModeTrue]
                have hNil : allZeroGoldilocks (if true = true then [] else [Goldilocks.one]) = true := by decide
                have hCtr0 : (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).tswCtr = lsig0.tswCtr := rfl
                refine allZeroGoldilocks_append_intro hNil
                  (allZeroGoldilocks_append_intro
                    (allZeroGoldilocks_append_intro
                      (allZeroGoldilocks_append_intro
                        (allZeroGoldilocks_append_intro hNil ?_) hW0Z) hUpZ)
                    ((lane4Sub_toList_allZero_iff _ _).mpr (hUpTop.trans hTopEq)))
                rw [hCtr0]
                exact hHmZ

/-! ### Symbolic Degree-≤7 Row Gate AST (`trace.rs:ConstraintKind`) & Degree-8 Sumcheck Bridge -/

/-- Algebraic row gate AST covering every constraint family in `crates/qsag-agg/src/trace.rs`
    (constant, boundary pin, linear wire equality, Boolean selector, conditional mux, quartic
    base-4 digit check, and septic `x^7` `Poseidon2` S-box). -/
inductive RowGate7 where
  | constGate (c : Goldilocks)
  | colSubConst (col : Nat) (c : Goldilocks)
  | colDiff (colA colB : Nat)
  | boolBitGate (col : Nat)
  | muxGate (selCol aCol bCol outCol : Nat)
  | quarticBase4Gate (col : Nat)
  | septicSboxGate (inCol : Nat) (rc : Goldilocks) (outCol : Nat)
  deriving DecidableEq, Repr

/-- Base-field evaluation of a `RowGate7` on column assignment `row : Nat → Goldilocks`. -/
def evalRowGate7 (g : RowGate7) (row : Nat → Goldilocks) : Goldilocks :=
  match g with
  | .constGate c => c
  | .colSubConst col c => Goldilocks.sub (row col) c
  | .colDiff colA colB => Goldilocks.sub (row colA) (row colB)
  | .boolBitGate col => boolBitResidual (row col)
  | .muxGate selCol aCol bCol outCol =>
    Goldilocks.sub (row outCol)
      (Goldilocks.add (row aCol) (Goldilocks.mul (row selCol) (Goldilocks.sub (row bCol) (row aCol))))
  | .quarticBase4Gate col => quarticBase4 (row col)
  | .septicSboxGate inCol rc outCol =>
    Goldilocks.sub (sbox7 (Goldilocks.add (row inCol) rc)) (row outCol)


/-! ### Public Statement, Boundary Pinning, Execution Trace, & `trace_satisfies_constraints_iff_all_k_sigs_valid` -/

/-- Public arithmetization statement `(geom, msg, committeePks, logRows)` binding `K ≥ 1` distinct
    committee public keys and message `msg` to hypercube dimension `logRows` (`2^logRows` rows). -/
structure AggArithPublicStmt where
  geom         : AggSigGeometry
  msg          : List UInt8
  committeePks : List AggValidatorPk
  logRows      : Nat
  deriving DecidableEq, Repr

@[expose] def AggArithPublicStmt.wellFormed (stmt : AggArithPublicStmt) : Bool :=
  stmt.geom.wellFormed &&
  !stmt.committeePks.isEmpty &&
  decide stmt.committeePks.Nodup &&
  decide (stmt.committeePks.length ≤ 2 ^ stmt.logRows) &&
  stmt.committeePks.all (·.profile == stmt.geom.profile)

/-- 14 public boundary field elements pinned on row `k` for `(pk, msg)`:
    column `0` is `profileFieldTag pk.profile ∈ {1, 2}` (strictly non-zero for every `pk`),
    columns `1..4` are `pk.pkSeed`, columns `5..8` are `pk.pkRoot`, and columns `9..13` are
    `computeMessageMu pk msg` (`Digest5`). -/
def expectedBoundaryCols (pk : AggValidatorPk) (msg : List UInt8) : List Goldilocks :=
  let mu := computeMessageMu pk msg
  [profileFieldTag pk.profile] ++ pk.pkSeed.toList ++ pk.pkRoot.toList ++
    [mu.limb0, mu.limb1, mu.limb2, mu.limb3, mu.limb4]
#export_eqns expectedBoundaryCols

def boundaryGatesFrom (idx : Nat) : List Goldilocks → List RowGate7
  | [] => []
  | c :: cs => RowGate7.colSubConst idx c :: boundaryGatesFrom (idx + 1) cs

/-- Exact `RowGate7.colSubConst` boundary constraints for validator `pk` and `msg`. -/
@[expose] def boundaryRowGates (pk : AggValidatorPk) (msg : List UInt8) : List RowGate7 :=
  boundaryGatesFrom 0 (expectedBoundaryCols pk msg)

/-- Evaluate a list of `RowGate7` gates on a concrete row `List Goldilocks`. -/
def evalRowGateList (gates : List RowGate7) (row : List Goldilocks) : List Goldilocks :=
  gates.map (fun g => evalRowGate7 g (fun col => row.getD col Goldilocks.zero))

theorem boundaryGatesFrom_zero_at_col0 (c0 : Goldilocks) (cs : List Goldilocks)
    (row : List Goldilocks)
    (hZero : allZeroGoldilocks (evalRowGateList (boundaryGatesFrom 0 (c0 :: cs)) row) = true) :
    row.getD 0 Goldilocks.zero = c0 := by
  unfold boundaryGatesFrom evalRowGateList allZeroGoldilocks at hZero
  simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hZero
  exact (sub_eq_zero_iff_goldilocks _ _).mp hZero.1

theorem boundaryGatesFrom_exact :
    ∀ (idx : Nat) (expected pfx sfx : List Goldilocks),
      pfx.length = idx →
      allZeroGoldilocks (evalRowGateList (boundaryGatesFrom idx expected) (pfx ++ expected ++ sfx)) = true
  | _, [], _, _, _ => rfl
  | idx, c :: cs, pfx, sfx, hLen => by
    have hGet : (pfx ++ (c :: cs) ++ sfx).getD idx Goldilocks.zero = c := by
      have hAssoc : pfx ++ (c :: cs) ++ sfx = pfx ++ (c :: (cs ++ sfx)) := by
        simp [List.append_assoc]
      rw [hAssoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hLen]
    have hSub : pfx ++ (c :: cs) ++ sfx = (pfx ++ [c]) ++ cs ++ sfx := by
      simp [List.append_assoc]
    have ih := boundaryGatesFrom_exact (idx + 1) cs (pfx ++ [c]) sfx (by simp [hLen])
    unfold evalRowGateList allZeroGoldilocks at ih ⊢
    simp only [boundaryGatesFrom, List.map_cons, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · dsimp only [evalRowGate7]
      rw [hGet]
      exact (sub_eq_zero_iff_goldilocks c c).mpr rfl
    · rw [← hSub] at ih
      exact ih

theorem allZero_flatMap_replicate_zeros :
    ∀ (m n : Nat),
      allZeroGoldilocks ((List.replicate m (List.replicate n Goldilocks.zero)).flatMap id) = true
  | 0, _ => rfl
  | m + 1, n => by
    have hRepZero : ∀ k : Nat, allZeroGoldilocks (List.replicate k Goldilocks.zero) = true := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        unfold allZeroGoldilocks at ih ⊢
        simp only [List.replicate_succ, List.all_cons, beq_self_eq_true, Bool.true_and]
        exact ih
    simp only [List.replicate_succ, List.flatMap_cons, id_eq, allZeroGoldilocks_append, Bool.and_eq_true]
    exact ⟨hRepZero n, allZero_flatMap_replicate_zeros m n⟩

theorem getD_zero_replicate_zero (numCols : Nat) :
    (List.replicate numCols Goldilocks.zero).getD 0 Goldilocks.zero = Goldilocks.zero := by
  cases numCols <;> rfl

end Qsag
end
