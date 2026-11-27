module

public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.BlindVcVerifier
import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

/-- Reconstruct Round-1 `(com_0, com_1, com_2)` from an opened repetition (`blind_vc.rs:2388-2406`). -/
def reconstructRepCommits (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (o : OpenedBlindVcRep) : Triple3 (List UInt8) :=
  let comE := vcCommitPartyView H presNonce repIdx o.e o.viewE (vcPartyFinalOutAt o.finalOuts o.e)
  let comE1 := vcCommitPartyView H presNonce repIdx (vcNextParty3 o.e) o.viewE1
    (vcPartyFinalOutAt o.finalOuts (vcNextParty3 o.e))
  Triple3.ofFn (mkParty3At o.e comE comE1 o.unopenedCommit)

def reconstructRepRound1 (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (o : OpenedBlindVcRep) : Triple3 (List UInt8) × VcRepFinalOuts3 :=
  (reconstructRepCommits H presNonce repIdx o, o.finalOuts)

def reconstructAllRepRound1 (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32) :
    Nat → List OpenedBlindVcRep → List (Triple3 (List UInt8) × VcRepFinalOuts3)
  | _, [] => []
  | repIdx, o :: rest => reconstructRepRound1 H presNonce repIdx o ::
      reconstructAllRepRound1 H presNonce (repIdx + 1) rest

/-- Open a 3-party repetition bundle at challenge `e ∈ {0, 1, 2}`. -/
def openBlindVcRep (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (triple : BlindVcRepTriple) (e : Fin 3) : OpenedBlindVcRep :=
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  { e := e
    viewE := triple.views e
    viewE1 := triple.views e1
    unopenedCommit := vcCommitPartyView H presNonce repIdx e2 (triple.views e2)
      (vcPartyFinalOutAt triple.finalOuts e2)
    finalOuts := triple.finalOuts }

theorem reconstructRepRound1_openBlindVcRep (H : List UInt8 → List UInt8)
    (presNonce : Vec UInt8 32) (repIdx : Nat) (triple : BlindVcRepTriple) (e : Fin 3) :
    reconstructRepRound1 H presNonce repIdx (openBlindVcRep H presNonce repIdx triple e) =
      (Triple3.ofFn (fun i => vcCommitPartyView H presNonce repIdx i (triple.views i)
         (vcPartyFinalOutAt triple.finalOuts i)),
       triple.finalOuts) := by
  unfold reconstructRepRound1 reconstructRepCommits openBlindVcRep
  dsimp only
  refine Prod.ext ?_ rfl
  apply Triple3.ext_get
  intro i
  rw [Triple3.get_ofFn, Triple3.get_ofFn]
  let f : Fin 3 → List UInt8 := fun j =>
    vcCommitPartyView H presNonce repIdx j (triple.views j) (vcPartyFinalOutAt triple.finalOuts j)
  change mkParty3At e (f e) (f (vcNextParty3 e)) (f (vcUnopenedParty3 e)) i = f i
  rw [mkParty3At_eta]

/-- Serialize public selective-disclosure statement + Round-1 bundle for Fiat-Shamir challenge derivation
    (`"QSAG.FS.INIT.V1"` + `"QSAG.FS.ABSORB.V1"` + `"QSAG.FS.SQUEEZE.V1"`, `blind_vc.rs:2152-2418`). -/
private def serDisclosedFrames : List (Nat × Goldilocks) → List (List UInt8)
  | [] => [[0x00]]
  | (idx, val) :: rest => [([0x01] : List UInt8), encodeNatLeBytes 8 idx, encodeGoldilocksVecLe [val]].flatten ::
      serDisclosedFrames rest

private def serRound1ItemFrames (item : Triple3 (List UInt8) × VcRepFinalOuts3) : List (List UInt8) :=
  [item.1.s0, item.1.s1, item.1.s2] ++
  serLane6Frame item.2.rootShares.s0 ++ serLane6Frame item.2.rootShares.s1 ++ serLane6Frame item.2.rootShares.s2 ++
  serLane6Frame item.2.presShares.s0 ++ serLane6Frame item.2.presShares.s1 ++ serLane6Frame item.2.presShares.s2 ++
  serLane6Frame item.2.scopeShares.s0 ++ serLane6Frame item.2.scopeShares.s1 ++ serLane6Frame item.2.scopeShares.s2 ++
  (item.2.boolZeroShares.map (fun t => encodeGoldilocksVecLe [t.s0, t.s1, t.s2]))

def deriveBlindVcTranscriptDigest (H : List UInt8 → List UInt8)
    (verifierChallenge : List UInt8) (profile : ZkSoundnessProfile)
    (expectedSchema : VcSchema) (treeDepth : Nat)
    (presNonce issuerRootTag : Vec UInt8 32) (issuerEpoch : UInt64)
    (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
    (disclosed : List (Nat × Goldilocks))
    (allRound1 : List (Triple3 (List UInt8) × VcRepFinalOuts3)) : List UInt8 :=
  let profileTag := match profile with
    | .quantum128 => vcProfileQuantumTag
    | .classical128 => []
  let initDigest := H (cshake256FramedPreimage vcFsInitTag
    ([vcSdZkDomainTag, profileTag,
      encodeNatLeBytes 8 expectedSchema.schemaId.toNat,
      encodeNatLeBytes 8 expectedSchema.arity,
      leb128 treeDepth,
      encodeNatLeBytes 8 profile.repetitions,
      presNonce.toList,
      encodeNatLeBytes 8 issuerEpoch.toNat,
      issuerRootTag.toList,
      verifierChallenge] ++
     serLane6Frame accRoot ++ serLane6Frame presCommit ++ serLane6Frame scopeTag ++
     serLane4Frame verifierScopeLimbs ++ serDisclosedFrames disclosed))
  let r1Digest := foldFramesHash H vcFsAbsorbTag
    (allRound1.foldr (fun it acc => serRound1ItemFrames it ++ acc) [])
  H (cshake256FramedPreimage vcFsAbsorbTag [initDigest, r1Digest])

def deriveBlindVcChallengeAt (H : List UInt8 → List UInt8)
    (trDigest : List UInt8) (repIdx : Nat) : Fin 3 :=
  let sq := H (cshake256FramedPreimage vcFsSqueezeTag (vcChallengeContext204 trDigest repIdx))
  ⟨decodeNatLeBytes (sq.take 8) % 3, Nat.mod_lt _ (by decide)⟩

/-- Check all boolean-gate output wire shares: each `(z_0, z_1, z_2)` sums to `0` and matches `(z_e, z_{e+1})`. -/
def checkBoolZeroOutputs (e : Fin 3) :
    List (Goldilocks × Goldilocks) → List (Triple3 Goldilocks) → Bool
  | [], [] => true
  | (ze, ze1) :: restPairs, tz :: restTriples =>
    decide (tz.get e = ze) &&
    decide (tz.get (vcNextParty3 e) = ze1) &&
    decide (vcSum3 tz.get = Goldilocks.zero) &&
    checkBoolZeroOutputs e restPairs restTriples
  | _, _ => false

theorem checkBoolZeroOutputs_spec (e : Fin 3) :
    ∀ (pairs : List (Goldilocks × Goldilocks)) (triples : List (Triple3 Goldilocks)),
      checkBoolZeroOutputs e pairs triples = true ↔
        pairs = triples.map (fun t => vcPairAt t.get e) ∧
        (∀ t ∈ triples, vcSum3 t.get = Goldilocks.zero)
  | [], [] => by simp [checkBoolZeroOutputs]
  | [], _ :: _ => by simp [checkBoolZeroOutputs]
  | _ :: _, [] => by simp [checkBoolZeroOutputs]
  | (ze, ze1) :: ps, tz :: ts => by
    simp only [checkBoolZeroOutputs, Bool.and_eq_true, decide_eq_true_eq, List.map, List.cons.injEq]
    rw [checkBoolZeroOutputs_spec e ps ts]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hSum⟩, hPs, hAll⟩
      refine ⟨⟨Prod.ext h1.symm h2.symm, hPs⟩, ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | hTail
      · exact hSum
      · exact hAll t hTail
    · rintro ⟨⟨hHead, hPs⟩, hAll⟩
      injection hHead with h1 h2
      exact ⟨⟨⟨h1.symm, h2.symm⟩, hAll tz (.head ts)⟩, hPs, fun t ht => hAll t (.tail tz ht)⟩

/-- Construct 2-party rate-6 commit chunks for `pairCheckSponge3Perm` (`vcAttrCommitTag` / `vcPresCommitTag`). -/
def vcPairCommitChunks (e : Fin 3) (schema : VcSchema)
    (attrsE attrsE1 : List Goldilocks) (blindE blindE1 : Lane4) (tag : UInt64) :
    (Lane6 × Lane6) × (Lane6 × Lane6) × (Lane6 × Lane6) :=
  let sLo := vcConstPair e (vcSchemaLo schema.schemaId)
  let sHi := vcConstPair e (vcSchemaHiWithTag schema.schemaId tag)
  let sAr := vcConstPair e (Goldilocks.ofNat schema.arity)
  let sOne := vcConstPair e Goldilocks.one
  let c0 : Lane6 × Lane6 :=
    (⟨vcAttrAt attrsE 0, vcAttrAt attrsE 1, vcAttrAt attrsE 2,
      vcAttrAt attrsE 3, vcAttrAt attrsE 4, vcAttrAt attrsE 5⟩,
     ⟨vcAttrAt attrsE1 0, vcAttrAt attrsE1 1, vcAttrAt attrsE1 2,
      vcAttrAt attrsE1 3, vcAttrAt attrsE1 4, vcAttrAt attrsE1 5⟩)
  let c1 : Lane6 × Lane6 :=
    (⟨blindE.x0, blindE.x1, blindE.x2, blindE.x3, sLo.1, sHi.1⟩,
     ⟨blindE1.x0, blindE1.x1, blindE1.x2, blindE1.x3, sLo.2, sHi.2⟩)
  let c2 : Lane6 × Lane6 :=
    (⟨sAr.1, sOne.1, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
     ⟨sAr.2, sOne.2, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)
  (c0, c1, c2)

/-- Construct 2-party rate-6 scope chunks for `pairCheckSponge3Perm` (`vcScopeTagDom`). -/
def vcPairScopeChunks (e : Fin 3) (sid : UInt64)
    (hbE hbE1 : Lane4) (scopeLimbs : Lane4) :
    (Lane6 × Lane6) × (Lane6 × Lane6) × (Lane6 × Lane6) :=
  let sc0 := vcConstPair e scopeLimbs.x0
  let sc1 := vcConstPair e scopeLimbs.x1
  let sc2 := vcConstPair e scopeLimbs.x2
  let sc3 := vcConstPair e scopeLimbs.x3
  let sLo := vcConstPair e (vcSchemaLo sid)
  let sHi := vcConstPair e (vcSchemaHiWithTag sid vcScopeTagDom)
  let sOne := vcConstPair e Goldilocks.one
  let c0 : Lane6 × Lane6 :=
    (⟨hbE.x0, hbE.x1, hbE.x2, hbE.x3, sc0.1, sc1.1⟩,
     ⟨hbE1.x0, hbE1.x1, hbE1.x2, hbE1.x3, sc0.2, sc1.2⟩)
  let c1 : Lane6 × Lane6 :=
    (⟨sc2.1, sc3.1, Goldilocks.zero, Goldilocks.zero, sLo.1, sHi.1⟩,
     ⟨sc2.2, sc3.2, Goldilocks.zero, Goldilocks.zero, sLo.2, sHi.2⟩)
  let c2 : Lane6 × Lane6 :=
    (⟨sOne.1, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
     ⟨sOne.2, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)
  (c0, c1, c2)

/-- Full per-repetition ZKBoo verifier (`blind_vc.rs:2180-2415`):
    enforces challenge match `o.e = expectedE`, strict ascending `disclosed`, `attrShares.length = schema.arity`,
    pinned disclosed shares, PRG tape replay (`checkPartyPrgTape`) on BOTH `viewE` and `viewE1`,
    all 4 `absorbRate6Sponge3` / `treeDepth` Merkle subcircuits, and 3-share output reconstruction. -/
def verifyOpenedBlindVcRep
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (schema : VcSchema) (issuerEpoch : UInt64) (treeDepth : Nat)
    (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
    (disclosed : List (Nat × Goldilocks))
    (repIdx : Nat) (expectedE : Fin 3) (o : OpenedBlindVcRep) : Bool :=
  let e := o.e
  let e1 := vcNextParty3 e
  if !(decide (e = expectedE) &&
       vcCheckDisclosedStrictAsc schema.arity disclosed &&
       decide (o.viewE.attrShares.length = schema.arity) &&
       decide (o.viewE1.attrShares.length = schema.arity) &&
       decide (o.viewE.merkleLevels.length = treeDepth) &&
       decide (o.viewE1.merkleLevels.length = treeDepth) &&
       vcCheckPartyDisclosedShares e o.viewE.attrShares disclosed &&
       vcCheckPartyDisclosedShares e1 o.viewE1.attrShares disclosed &&
       checkPartyPrgTape prgExpand treeDepth repIdx e o.viewE &&
       checkPartyPrgTape prgExpand treeDepth repIdx e1 o.viewE1) then
    false
  else
    let (ac0, ac1, ac2) := vcPairCommitChunks e schema
      o.viewE.attrShares o.viewE1.attrShares
      o.viewE.holderBlindShare o.viewE1.holderBlindShare vcAttrCommitTag
    let (pc0, pc1, pc2) := vcPairCommitChunks e schema
      o.viewE.attrShares o.viewE1.attrShares
      o.viewE.presBlindShare o.viewE1.presBlindShare vcPresCommitTag
    let (sc0, sc1, sc2) := vcPairScopeChunks e schema.schemaId
      o.viewE.holderBlindShare o.viewE1.holderBlindShare verifierScopeLimbs
    match pairCheckSponge3Perm e o.viewE.attrSponge o.viewE1.attrSponge ac0 ac1 ac2,
          pairCheckSponge3Perm e o.viewE.presSponge o.viewE1.presSponge pc0 pc1 pc2,
          pairCheckSponge3Perm e o.viewE.scopeSponge o.viewE1.scopeSponge sc0 sc1 sc2 with
    | some leafPair, some presPair, some scopePair =>
      match pairCheckMerklePath e issuerEpoch 0 leafPair o.viewE.merkleLevels o.viewE1.merkleLevels with
      | none => false
      | some (rootPair, boolZeroPairs) =>
        decide (vcPairAtLane6 o.finalOuts.rootShares.get e = rootPair) &&
        decide (vcSumLane6_3 o.finalOuts.rootShares.get = accRoot) &&
        decide (vcPairAtLane6 o.finalOuts.presShares.get e = presPair) &&
        decide (vcSumLane6_3 o.finalOuts.presShares.get = presCommit) &&
        decide (vcPairAtLane6 o.finalOuts.scopeShares.get e = scopePair) &&
        decide (vcSumLane6_3 o.finalOuts.scopeShares.get = scopeTag) &&
        checkBoolZeroOutputs e boolZeroPairs o.finalOuts.boolZeroShares
    | _, _, _ => false

def verifyAllBlindVcReps
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (trDigest : List UInt8)
    (schema : VcSchema) (issuerEpoch : UInt64) (treeDepth : Nat)
    (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
    (disclosed : List (Nat × Goldilocks)) :
    Nat → List OpenedBlindVcRep → Bool
  | _, [] => true
  | repIdx, o :: rest =>
    let expectedE := deriveBlindVcChallengeAt H trDigest repIdx
    verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expectedE o &&
    verifyAllBlindVcReps H prgExpand trDigest schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed (repIdx + 1) rest

/-- Full selective-disclosure presentation verifier (`verify_presentation_with_profile`,
    `blind_vc.rs:2120-2425`):
    enforces `schemaId` match, strict ascending `disclosedAttrs` (`< arity` + `Nodup`),
    `openedReps.length = profile.repetitions` (`438` for `.quantum128`, `219` for `.classical128`),
    Round-1 `"QSAG.VC.VIEW_COM.V1"` + `"QSAG.COMMIT.V1"` commitment reconstruction,
    `"QSAG.FS.INIT/ABSORB/SQUEEZE.V1"` Fiat-Shamir challenge derivation, and PRG-checked ZKBoo replay!
    The accumulator root, issuer tag, epoch and verifier scope are read from `pres`, so this
    function checks a presentation against the context it carries. A relying party uses
    `verifyBlindVcPresentationTrusted`, which fixes that context first. -/
@[expose] def verifyBlindVcPresentation
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (expectedSchema : VcSchema) (treeDepth : Nat)
    (verifierChallenge : List UInt8)
    (pres : BlindVcPresentation) : Bool :=
  if !(decide (pres.schemaId = expectedSchema.schemaId) &&
       vcCheckDisclosedStrictAsc expectedSchema.arity pres.disclosedAttrs &&
       decide (pres.openedReps.length = profile.repetitions)) then
    false
  else
    let allRound1 := reconstructAllRepRound1 H pres.presentationNonce 0 pres.openedReps
    let trDigest := deriveBlindVcTranscriptDigest H verifierChallenge profile expectedSchema treeDepth
      pres.presentationNonce pres.issuerRootTag pres.issuerEpoch
      pres.accumulatorRoot pres.presCommit pres.scopeTag pres.verifierScopeLimbs
      pres.disclosedAttrs allRound1
    verifyAllBlindVcReps H prgExpand trDigest expectedSchema pres.issuerEpoch treeDepth
      pres.accumulatorRoot pres.presCommit pres.scopeTag pres.verifierScopeLimbs
      pres.disclosedAttrs 0 pres.openedReps

/-- Reconstruct the secret attribute list `[a_0, ..., a_{arity-1}]` from a 3-party view triple. -/
def vcReconstructAttrs3 (arity : Nat) (v : Fin 3 → PartyVcRepView) : List Goldilocks :=
  (List.range arity).map (fun k => vcSum3 (fun i => vcAttrAt (v i).attrShares k))

private theorem vcReconstructAttrs3_length (arity : Nat) (v : Fin 3 → PartyVcRepView) :
    (vcReconstructAttrs3 arity v).length = arity := by
  simp [vcReconstructAttrs3]

private theorem vcAttrAt_reconstructAttrs3 {arity : Nat} {v : Fin 3 → PartyVcRepView}
    (hLen : ∀ i : Fin 3, ((v i).attrShares).length = arity) (k : Nat) :
    vcAttrAt (vcReconstructAttrs3 arity v) k = vcSum3 (fun i => vcAttrAt (v i).attrShares k) := by
  unfold vcReconstructAttrs3
  if hk : k < arity then
    have hkRange : k < (List.range arity).length := by simp [hk]
    rw [vcAttrAt.public_eq_1]
    rw [List.getElem?_map, List.getElem?_eq_getElem hkRange, List.getElem_range]
    rfl
  else
    have hkRange : ((List.range arity).map (fun idx => vcSum3 (fun i => vcAttrAt (v i).attrShares idx)))[k]? = none := by
      apply List.getElem?_eq_none
      simp; omega
    have hLhs : vcAttrAt ((List.range arity).map (fun idx => vcSum3 (fun i => vcAttrAt (v i).attrShares idx))) k = Goldilocks.zero := by
      simp only [vcAttrAt.public_eqs] at hkRange ⊢
      rw [hkRange]
      rfl
    rw [hLhs]
    have hNone : ∀ i : Fin 3, ((v i).attrShares)[k]? = none := fun i => by
      apply List.getElem?_eq_none
      rw [hLen i]; omega
    have hFun0 : (fun i => vcAttrAt (v i).attrShares k) = (fun _ => Goldilocks.zero) := by
      funext i; rw [vcAttrAt.public_eq_1]; rw [hNone i]; rfl
    rw [hFun0, vcSum3_zero]

def vcCommitChunks3 (schema : VcSchema) (attrShares : Fin 3 → List Goldilocks)
    (blindShares : VcLane4_3) (tag : UInt64) : VcLane6_3 × VcLane6_3 × VcLane6_3 :=
  (fun i =>
    ⟨vcAttrAt (attrShares i) 0, vcAttrAt (attrShares i) 1, vcAttrAt (attrShares i) 2,
     vcAttrAt (attrShares i) 3, vcAttrAt (attrShares i) 4, vcAttrAt (attrShares i) 5⟩,
   fun i =>
    ⟨(blindShares i).x0, (blindShares i).x1, (blindShares i).x2, (blindShares i).x3,
     vcConstWire3 (vcSchemaLo schema.schemaId) i,
     vcConstWire3 (vcSchemaHiWithTag schema.schemaId tag) i⟩,
   fun i =>
    ⟨vcConstWire3 (Goldilocks.ofNat schema.arity) i,
     vcConstWire3 Goldilocks.one i,
     Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

theorem vcPairCommitChunks_spec (e : Fin 3) (schema : VcSchema)
    (attrShares : Fin 3 → List Goldilocks) (blindShares : VcLane4_3) (tag : UInt64) :
    vcPairCommitChunks e schema (attrShares e) (attrShares (vcNextParty3 e))
      (blindShares e) (blindShares (vcNextParty3 e)) tag =
      let (c0, c1, c2) := vcCommitChunks3 schema attrShares blindShares tag
      (vcPairAtLane6 c0 e, vcPairAtLane6 c1 e, vcPairAtLane6 c2 e) := by
  unfold vcPairCommitChunks vcCommitChunks3
  rw [vcConstPair_spec (vcSchemaLo schema.schemaId) e,
      vcConstPair_spec (vcSchemaHiWithTag schema.schemaId tag) e,
      vcConstPair_spec (Goldilocks.ofNat schema.arity) e,
      vcConstPair_spec Goldilocks.one e]
  rfl

def vcScopeChunks3 (sid : UInt64) (hbShares : VcLane4_3) (scopeLimbs : Lane4) :
    VcLane6_3 × VcLane6_3 × VcLane6_3 :=
  (fun i =>
    ⟨(hbShares i).x0, (hbShares i).x1, (hbShares i).x2, (hbShares i).x3,
     vcConstWire3 scopeLimbs.x0 i, vcConstWire3 scopeLimbs.x1 i⟩,
   fun i =>
    ⟨vcConstWire3 scopeLimbs.x2 i, vcConstWire3 scopeLimbs.x3 i,
     Goldilocks.zero, Goldilocks.zero,
     vcConstWire3 (vcSchemaLo sid) i, vcConstWire3 (vcSchemaHiWithTag sid vcScopeTagDom) i⟩,
   fun i =>
    ⟨vcConstWire3 Goldilocks.one i, Goldilocks.zero, Goldilocks.zero,
     Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

theorem vcPairScopeChunks_spec (e : Fin 3) (sid : UInt64)
    (hbShares : VcLane4_3) (scopeLimbs : Lane4) :
    vcPairScopeChunks e sid (hbShares e) (hbShares (vcNextParty3 e)) scopeLimbs =
      let (c0, c1, c2) := vcScopeChunks3 sid hbShares scopeLimbs
      (vcPairAtLane6 c0 e, vcPairAtLane6 c1 e, vcPairAtLane6 c2 e) := by
  unfold vcPairScopeChunks vcScopeChunks3
  rw [vcConstPair_spec scopeLimbs.x0 e, vcConstPair_spec scopeLimbs.x1 e,
      vcConstPair_spec scopeLimbs.x2 e, vcConstPair_spec scopeLimbs.x3 e,
      vcConstPair_spec (vcSchemaLo sid) e, vcConstPair_spec (vcSchemaHiWithTag sid vcScopeTagDom) e,
      vcConstPair_spec Goldilocks.one e]
  rfl

/- **Constructive 3-Challenge Special Soundness + Round-1 Commitment Extraction (`0 Classical.choice`)**:
    Given 3 accepting openings `(o0, o1, o2)` at challenges `(0, 1, 2)` sharing the SAME Round-1
    `(commits, finalOuts)` transcript (with ZERO external `Nodup` assumption — derived directly from
    `verifyOpenedBlindVcRep`!), **either** an explicit `H`-collision is constructively exhibited,
    **or** a complete valid credential + boolean Merkle witness `(attrs, holderBlind, presBlind, leafCommit, boolSteps)`
    is extracted! -/
/-- A collision in one of the three concrete overlapping view pairs of a rewound table.
This finite event says nothing about collisions at unrelated hash inputs. -/
@[expose] def VcRewoundCommitConflict (H : List UInt8 → List UInt8)
    (nonce : Vec UInt8 32) (repIdx : Nat) (o0 o1 o2 : OpenedBlindVcRep) : Prop :=
  (o0.viewE1 ≠ o1.viewE ∧
    vcCommitPartyView H nonce repIdx 1 o0.viewE1 (vcPartyFinalOutAt o1.finalOuts 1) =
    vcCommitPartyView H nonce repIdx 1 o1.viewE (vcPartyFinalOutAt o1.finalOuts 1)) ∨
  (o1.viewE1 ≠ o2.viewE ∧
    vcCommitPartyView H nonce repIdx 2 o1.viewE1 (vcPartyFinalOutAt o2.finalOuts 2) =
    vcCommitPartyView H nonce repIdx 2 o2.viewE (vcPartyFinalOutAt o2.finalOuts 2)) ∨
  (o2.viewE1 ≠ o0.viewE ∧
    vcCommitPartyView H nonce repIdx 0 o2.viewE1 (vcPartyFinalOutAt o0.finalOuts 0) =
    vcCommitPartyView H nonce repIdx 0 o0.viewE (vcPartyFinalOutAt o0.finalOuts 0))

instance (H : List UInt8 → List UInt8) (nonce : Vec UInt8 32)
    (repIdx : Nat) (o0 o1 o2 : OpenedBlindVcRep) :
    Decidable (VcRewoundCommitConflict H nonce repIdx o0 o1 o2) :=
  by unfold VcRewoundCommitConflict; infer_instance

/-- The finite event identifies which actual committed view pair breaks binding. -/
theorem vcRewoundCommitConflict_hash_collision
    {H : List UInt8 → List UInt8} (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {nonce : Vec UInt8 32} {repIdx : Nat} {o0 o1 o2 : OpenedBlindVcRep}
    (h : VcRewoundCommitConflict H nonce repIdx o0 o1 o2) :
    ∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂ := by
  rcases h with h | h | h
  all_goals exact vcCommitPartyView_binding hHLen (fun he => h.1 (congrArg Prod.fst he)) h.2

theorem verifyOpenedBlindVcRep_extract3_finite_conflict
    {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {presNonce : Vec UInt8 32} {schema : VcSchema} {issuerEpoch : UInt64} {treeDepth : Nat}
    {accRoot presCommit scopeTag : Lane6} {verifierScopeLimbs : Lane4}
    {disclosed : List (Nat × Goldilocks)} {repIdx : Nat}
    {o0 o1 o2 : OpenedBlindVcRep}
    (hR1_01 : reconstructRepRound1 H presNonce repIdx o0 = reconstructRepRound1 H presNonce repIdx o1)
    (hR1_12 : reconstructRepRound1 H presNonce repIdx o1 = reconstructRepRound1 H presNonce repIdx o2)
    (hVer0 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 0 o0 = true)
    (hVer1 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 1 o1 = true)
    (hVer2 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 2 o2 = true) :
    VcRewoundCommitConflict H presNonce repIdx o0 o1 o2 ∨
    ∃ (attrs : List Goldilocks) (holderBlind presBlind : Lane4)
      (leafCommit : Lane6) (boolSteps : List (Bool × Lane6)),
      (disclosed.map Prod.fst).Nodup ∧
      attrs.length = schema.arity ∧
      (∀ p ∈ disclosed, p.1 < schema.arity ∧ attrs[p.1]? = some p.2) ∧
      computeVcPoseidon2Commit schema attrs holderBlind vcAttrCommitTag = some leafCommit ∧
      boolSteps.length = treeDepth ∧
      evalVcMerklePathBool issuerEpoch 0 leafCommit boolSteps = accRoot ∧
      computeVcPoseidon2Commit schema attrs presBlind vcPresCommitTag = some presCommit ∧
      computeVcScopeTag schema.schemaId holderBlind verifierScopeLimbs = scopeTag := by
  have hUnpack : ∀ {expE : Fin 3} {o : OpenedBlindVcRep},
      verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
        accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expE o = true →
      o.e = expE ∧
      vcCheckDisclosedStrictAsc schema.arity disclosed = true ∧
      o.viewE.attrShares.length = schema.arity ∧
      o.viewE1.attrShares.length = schema.arity ∧
      o.viewE.merkleLevels.length = treeDepth := by
    intro expE o hV
    unfold verifyOpenedBlindVcRep at hV
    dsimp only at hV
    cases hG :
        (decide (o.e = expE) &&
         vcCheckDisclosedStrictAsc schema.arity disclosed &&
         decide (o.viewE.attrShares.length = schema.arity) &&
         decide (o.viewE1.attrShares.length = schema.arity) &&
         decide (o.viewE.merkleLevels.length = treeDepth) &&
         decide (o.viewE1.merkleLevels.length = treeDepth) &&
         vcCheckPartyDisclosedShares o.e o.viewE.attrShares disclosed &&
         vcCheckPartyDisclosedShares (vcNextParty3 o.e) o.viewE1.attrShares disclosed &&
         checkPartyPrgTape prgExpand treeDepth repIdx o.e o.viewE &&
         checkPartyPrgTape prgExpand treeDepth repIdx (vcNextParty3 o.e) o.viewE1) with
    | false => rw [hG] at hV; cases hV
    | true =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
      exact ⟨hG.1.1.1.1.1.1.1.1.1, hG.1.1.1.1.1.1.1.1.2,
             hG.1.1.1.1.1.1.1.2, hG.1.1.1.1.1.1.2, hG.1.1.1.1.1.2⟩
  obtain ⟨he0, hAsc, _, _, _⟩ := hUnpack hVer0
  obtain ⟨he1, _, _, _, _⟩ := hUnpack hVer1
  obtain ⟨he2, _, _, _, _⟩ := hUnpack hVer2
  have hFo01 : o0.finalOuts = o1.finalOuts := congrArg Prod.snd hR1_01
  have hFo12 : o1.finalOuts = o2.finalOuts := congrArg Prod.snd hR1_12
  have hCom01 : reconstructRepCommits H presNonce repIdx o0 = reconstructRepCommits H presNonce repIdx o1 :=
    congrArg Prod.fst hR1_01
  have hCom12 : reconstructRepCommits H presNonce repIdx o1 = reconstructRepCommits H presNonce repIdx o2 :=
    congrArg Prod.fst hR1_12
  if hv1 : o0.viewE1 ≠ o1.viewE then
    left
    have hc1 := congrArg (fun t => t.get 1) hCom01
    unfold reconstructRepCommits at hc1
    rw [he0, he1, hFo01, Triple3.get_ofFn, Triple3.get_ofFn] at hc1
    dsimp only [vcNextParty3, mkParty3At] at hc1
    exact Or.inl ⟨hv1, hc1⟩
  else if hv2 : o1.viewE1 ≠ o2.viewE then
    left
    have hc2 := congrArg (fun t => t.get 2) hCom12
    unfold reconstructRepCommits at hc2
    rw [he1, he2, hFo12, Triple3.get_ofFn, Triple3.get_ofFn] at hc2
    dsimp only [vcNextParty3, mkParty3At] at hc2
    exact Or.inr (Or.inl ⟨hv2, hc2⟩)
  else if hv0 : o2.viewE1 ≠ o0.viewE then
    left
    have hFo20 : o2.finalOuts = o0.finalOuts := (hFo01.trans hFo12).symm
    have hc0 := congrArg (fun t => t.get 0) (hCom01.trans hCom12).symm
    unfold reconstructRepCommits at hc0
    rw [he2, he0, hFo20, Triple3.get_ofFn, Triple3.get_ofFn] at hc0
    dsimp only [vcNextParty3, mkParty3At] at hc0
    exact Or.inr (Or.inr ⟨hv0, hc0⟩)
  else
    right
    have hv1Eq : o0.viewE1 = o1.viewE := Decidable.of_not_not hv1
    have hv2Eq : o1.viewE1 = o2.viewE := Decidable.of_not_not hv2
    have hv0Eq : o2.viewE1 = o0.viewE := Decidable.of_not_not hv0
    let v : Fin 3 → PartyVcRepView
      | ⟨0, _⟩ => o0.viewE
      | ⟨1, _⟩ => o1.viewE
      | ⟨2, _⟩ => o2.viewE
    let fo := o0.finalOuts
    have hStepBody : ∀ {expE : Fin 3} {o : OpenedBlindVcRep},
        o.e = expE → o.viewE = v expE → o.viewE1 = v (vcNextParty3 expE) → o.finalOuts = fo →
        verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
          accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expE o = true →
        (v expE).attrShares.length = schema.arity ∧
        (v expE).merkleLevels.length = treeDepth ∧
        vcCheckPartyDisclosedShares expE (v expE).attrShares disclosed = true ∧
        ∃ leafPair presPair scopePair boolZeroPairs,
          pairCheckSponge3Perm expE (v expE).attrSponge (v (vcNextParty3 expE)).attrSponge
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).holderBlindShare (v (vcNextParty3 expE)).holderBlindShare vcAttrCommitTag).1
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).holderBlindShare (v (vcNextParty3 expE)).holderBlindShare vcAttrCommitTag).2.1
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).holderBlindShare (v (vcNextParty3 expE)).holderBlindShare vcAttrCommitTag).2.2 = some leafPair ∧
          pairCheckSponge3Perm expE (v expE).presSponge (v (vcNextParty3 expE)).presSponge
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).presBlindShare (v (vcNextParty3 expE)).presBlindShare vcPresCommitTag).1
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).presBlindShare (v (vcNextParty3 expE)).presBlindShare vcPresCommitTag).2.1
            (vcPairCommitChunks expE schema (v expE).attrShares (v (vcNextParty3 expE)).attrShares
              (v expE).presBlindShare (v (vcNextParty3 expE)).presBlindShare vcPresCommitTag).2.2 = some presPair ∧
          pairCheckSponge3Perm expE (v expE).scopeSponge (v (vcNextParty3 expE)).scopeSponge
            (vcPairScopeChunks expE schema.schemaId (v expE).holderBlindShare
              (v (vcNextParty3 expE)).holderBlindShare verifierScopeLimbs).1
            (vcPairScopeChunks expE schema.schemaId (v expE).holderBlindShare
              (v (vcNextParty3 expE)).holderBlindShare verifierScopeLimbs).2.1
            (vcPairScopeChunks expE schema.schemaId (v expE).holderBlindShare
              (v (vcNextParty3 expE)).holderBlindShare verifierScopeLimbs).2.2 = some scopePair ∧
          pairCheckMerklePath expE issuerEpoch 0 leafPair
            (v expE).merkleLevels (v (vcNextParty3 expE)).merkleLevels =
              some (vcPairAtLane6 fo.rootShares.get expE, boolZeroPairs) ∧
          vcSumLane6_3 fo.rootShares.get = accRoot ∧
          vcPairAtLane6 fo.presShares.get expE = presPair ∧
          vcSumLane6_3 fo.presShares.get = presCommit ∧
          vcPairAtLane6 fo.scopeShares.get expE = scopePair ∧
          vcSumLane6_3 fo.scopeShares.get = scopeTag ∧
          checkBoolZeroOutputs expE boolZeroPairs fo.boolZeroShares = true := by
      intro expE o he hve hve1 hfo hV
      unfold verifyOpenedBlindVcRep at hV
      rw [he, hve, hve1, hfo] at hV
      dsimp only at hV
      cases hG :
          (decide (expE = expE) &&
           vcCheckDisclosedStrictAsc schema.arity disclosed &&
           decide ((v expE).attrShares.length = schema.arity) &&
           decide ((v (vcNextParty3 expE)).attrShares.length = schema.arity) &&
           decide ((v expE).merkleLevels.length = treeDepth) &&
           decide ((v (vcNextParty3 expE)).merkleLevels.length = treeDepth) &&
           vcCheckPartyDisclosedShares expE (v expE).attrShares disclosed &&
           vcCheckPartyDisclosedShares (vcNextParty3 expE) (v (vcNextParty3 expE)).attrShares disclosed &&
           checkPartyPrgTape prgExpand treeDepth repIdx expE (v expE) &&
           checkPartyPrgTape prgExpand treeDepth repIdx (vcNextParty3 expE) (v (vcNextParty3 expE))) with
      | false => rw [hG] at hV; cases hV
      | true =>
        rw [hG] at hV
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hV
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
        refine ⟨hG.1.1.1.1.1.1.1.2, hG.1.1.1.1.1.2, hG.1.1.1.2, ?_⟩
        cases ha : pairCheckSponge3Perm expE (v expE).attrSponge (v (vcNextParty3 expE)).attrSponge _ _ _ with
        | none => rw [ha] at hV; cases hV
        | some lp =>
        cases hp : pairCheckSponge3Perm expE (v expE).presSponge (v (vcNextParty3 expE)).presSponge _ _ _ with
        | none => rw [ha, hp] at hV; cases hV
        | some pp =>
        cases hs : pairCheckSponge3Perm expE (v expE).scopeSponge (v (vcNextParty3 expE)).scopeSponge _ _ _ with
        | none => rw [ha, hp, hs] at hV; cases hV
        | some sp =>
          rw [ha, hp, hs] at hV
          dsimp only at hV
          cases hm : pairCheckMerklePath expE issuerEpoch 0 lp (v expE).merkleLevels (v (vcNextParty3 expE)).merkleLevels with
          | none => rw [hm] at hV; cases hV
          | some mkOut =>
            rw [hm] at hV
            rcases mkOut with ⟨rp, bzp⟩
            dsimp only at hV
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hV
            rcases hV with ⟨⟨⟨⟨⟨⟨hRp, hAcc⟩, hPp⟩, hPres⟩, hSp⟩, hSc⟩, hBz⟩
            subst hRp
            exact ⟨lp, pp, sp, bzp, rfl, rfl, rfl, hm, hAcc, hPp, hPres, hSp, hSc, hBz⟩
    obtain ⟨hLen0, hMkLen0, hDisc0, lp0, pp0, sp0, bzp0, ha0, hp0, hs0, hm0, hAccSum, hPp0, hPresSum, hSp0, hScSum, hBz0⟩ :=
      hStepBody he0 rfl hv1Eq rfl hVer0
    obtain ⟨hLen1, _, hDisc1, lp1, pp1, sp1, bzp1, ha1, hp1, hs1, hm1, _, hPp1, _, hSp1, _, hBz1⟩ :=
      hStepBody he1 rfl hv2Eq hFo01.symm hVer1
    obtain ⟨hLen2, _, hDisc2, lp2, pp2, sp2, bzp2, ha2, hp2, hs2, hm2, _, hPp2, _, hSp2, _, _⟩ :=
      hStepBody he2 rfl hv0Eq (hFo01.trans hFo12).symm hVer2
    have hAllLen : ∀ i : Fin 3, ((v i).attrShares).length = schema.arity :=
      BlindVc.fin3_all hLen0 hLen1 hLen2
    rw [vcPairCommitChunks_spec 0 schema (fun i => (v i).attrShares) (fun i => (v i).holderBlindShare) vcAttrCommitTag] at ha0
    rw [vcPairCommitChunks_spec 1 schema (fun i => (v i).attrShares) (fun i => (v i).holderBlindShare) vcAttrCommitTag] at ha1
    rw [vcPairCommitChunks_spec 2 schema (fun i => (v i).attrShares) (fun i => (v i).holderBlindShare) vcAttrCommitTag] at ha2
    rw [vcPairCommitChunks_spec 0 schema (fun i => (v i).attrShares) (fun i => (v i).presBlindShare) vcPresCommitTag] at hp0
    rw [vcPairCommitChunks_spec 1 schema (fun i => (v i).attrShares) (fun i => (v i).presBlindShare) vcPresCommitTag] at hp1
    rw [vcPairCommitChunks_spec 2 schema (fun i => (v i).attrShares) (fun i => (v i).presBlindShare) vcPresCommitTag] at hp2
    rw [vcPairScopeChunks_spec 0 schema.schemaId (fun i => (v i).holderBlindShare) verifierScopeLimbs] at hs0
    rw [vcPairScopeChunks_spec 1 schema.schemaId (fun i => (v i).holderBlindShare) verifierScopeLimbs] at hs1
    rw [vcPairScopeChunks_spec 2 schema.schemaId (fun i => (v i).holderBlindShare) verifierScopeLimbs] at hs2
    obtain ⟨leaf3, hlp0, hlp1, hlp2, hLeafSum⟩ :=
      pairCheckSponge3Perm_extract3 (sv := fun i => (v i).attrSponge) ha0 ha1 ha2
    obtain ⟨pres3, hpp0', hpp1', _, hPresSpongeSum⟩ :=
      pairCheckSponge3Perm_extract3 (sv := fun i => (v i).presSponge) hp0 hp1 hp2
    obtain ⟨scope3, hsp0', hsp1', _, hScopeSpongeSum⟩ :=
      pairCheckSponge3Perm_extract3 (sv := fun i => (v i).scopeSponge) hs0 hs1 hs2
    rw [hlp0] at hm0; rw [hlp1] at hm1; rw [hlp2] at hm2
    obtain ⟨root3, bzs3, arithSteps, hArithLen, hmr0, hmr1, _, hBoolGateImp, hRootMerkleSum⟩ :=
      pairCheckMerklePath_extract3 issuerEpoch treeDepth 0 leaf3 (fun i => (v i).merkleLevels) hMkLen0 hm0 hm1 hm2
    have hPresEq : fo.presShares.get = pres3 := by
      have e0 := hPp0.trans hpp0'
      have e1 := hPp1.trans hpp1'
      exact funext (BlindVc.fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1))
    have hScopeEq : fo.scopeShares.get = scope3 := by
      have e0 := hSp0.trans hsp0'
      have e1 := hSp1.trans hsp1'
      exact funext (BlindVc.fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1))
    have hRootEq : fo.rootShares.get = root3 := by
      have e0 := congrArg Prod.fst hmr0
      have e1 := congrArg Prod.fst hmr1
      exact funext (BlindVc.fin3_all (congrArg Prod.fst e0) (congrArg Prod.snd e0) (congrArg Prod.snd e1))
    obtain ⟨hBzp0Eq, hFoBoolZero⟩ := (checkBoolZeroOutputs_spec 0 bzp0 fo.boolZeroShares).mp hBz0
    obtain ⟨hBzp1Eq, _⟩ := (checkBoolZeroOutputs_spec 1 bzp1 fo.boolZeroShares).mp hBz1
    have hBzsZero : ∀ z ∈ bzs3, vcSum3 z = Goldilocks.zero := by
      have hMap0 : fo.boolZeroShares.map (fun t => vcPairAt t.get 0) = bzs3.map (fun w => vcPairAt w 0) :=
        hBzp0Eq.symm.trans (congrArg Prod.snd hmr0)
      have hMap1 : fo.boolZeroShares.map (fun t => vcPairAt t.get 1) = bzs3.map (fun w => vcPairAt w 1) :=
        hBzp1Eq.symm.trans (congrArg Prod.snd hmr1)
      have hZipGet : ∀ (ts : List (Triple3 Goldilocks)) (ws : List VcWire3),
          ts.map (fun t => vcPairAt t.get 0) = ws.map (fun w => vcPairAt w 0) →
          ts.map (fun t => vcPairAt t.get 1) = ws.map (fun w => vcPairAt w 1) →
          ts.map Triple3.get = ws := by
        intro ts
        induction ts with
        | nil =>
          intro ws hM0 _
          cases ws with
          | nil => rfl
          | cons _ _ => cases hM0
        | cons t ts ih =>
          intro ws hM0 hM1
          cases ws with
          | nil => cases hM0
          | cons w ws =>
            dsimp only [List.map] at hM0 hM1 ⊢
            injection hM0 with hw0 hRest0
            injection hM1 with hw1 hRest1
            have htw : t.get = w :=
              funext (BlindVc.fin3_all (congrArg Prod.fst hw0) (congrArg Prod.snd hw0) (congrArg Prod.snd hw1))
            rw [htw, ih ws hRest0 hRest1]
      have hListEq := hZipGet fo.boolZeroShares bzs3 hMap0 hMap1
      rw [← hListEq]
      intro z hz
      obtain ⟨t, htMem, rfl⟩ := List.mem_map.mp hz
      exact hFoBoolZero t htMem
    obtain ⟨boolSteps, hBoolStepsLen, hEvalBool⟩ :=
      evalVcMerklePathFrom_eq_bool issuerEpoch 0 (vcSumLane6_3 leaf3) arithSteps (hBoolGateImp hBzsZero)
    obtain ⟨hBounds, hNodup⟩ := vcCheckDisclosedStrictAsc_bounds_and_nodup hAsc
    let attrs := vcReconstructAttrs3 schema.arity v
    let holderBlind := vcSumLane4_3 (fun i => (v i).holderBlindShare)
    let presBlind := vcSumLane4_3 (fun i => (v i).presBlindShare)
    have hAttrsLen : attrs.length = schema.arity := vcReconstructAttrs3_length schema.arity v
    have hChunksSum : ∀ (blindShares : VcLane4_3) (tag : UInt64),
        let (c0, c1, c2) := vcCommitChunks3 schema (fun i => (v i).attrShares) blindShares tag
        (vcSumLane6_3 c0, vcSumLane6_3 c1, vcSumLane6_3 c2) =
          vcCommitChunks schema attrs (vcSumLane4_3 blindShares) tag := by
      intro blindShares tag
      unfold vcCommitChunks3
      rw [vcCommitChunks.public_eq_1]
      dsimp only
      simp only [vcSumLane6_3_eq, vcSumLane4_3_eq, vcSum3_constWire, vcSum3_zero,
        ← vcAttrAt_reconstructAttrs3 hAllLen]
      rfl
    have hScopeChunksSum :
        let (c0, c1, c2) := vcScopeChunks3 schema.schemaId (fun i => (v i).holderBlindShare) verifierScopeLimbs
        (vcSumLane6_3 c0, vcSumLane6_3 c1, vcSumLane6_3 c2) =
          vcScopeChunks schema.schemaId holderBlind verifierScopeLimbs := by
      unfold vcScopeChunks3
      rw [vcScopeChunks.public_eq_1]
      dsimp only [holderBlind]
      simp only [vcSumLane6_3_eq, vcSumLane4_3_eq, vcSum3_constWire, vcSum3_zero]
    refine ⟨attrs, holderBlind, presBlind, vcSumLane6_3 leaf3, boolSteps,
      hNodup, hAttrsLen, ?_, ?_, hBoolStepsLen.trans hArithLen, ?_, ?_, ?_⟩
    · intro p hp
      have hpLt : p.1 < schema.arity := hBounds p hp
      refine ⟨hpLt, ?_⟩
      have h0p := vcCheckPartyDisclosedShares_mem hDisc0 p hp
      have h1p := vcCheckPartyDisclosedShares_mem hDisc1 p hp
      have h2p := vcCheckPartyDisclosedShares_mem hDisc2 p hp
      have hpRange : p.1 < (List.range schema.arity).length := by simp [hpLt]
      dsimp only [attrs, vcReconstructAttrs3]
      rw [List.getElem?_map, List.getElem?_eq_getElem hpRange, List.getElem_range]
      apply congrArg some
      have ha0Eq : vcAttrAt (v 0).attrShares p.1 = vcExpectedDisclosedShare 0 p.2 := by
        rw [vcAttrAt.public_eq_1]; rw [h0p]; rfl
      have ha1Eq : vcAttrAt (v 1).attrShares p.1 = vcExpectedDisclosedShare 1 p.2 := by
        rw [vcAttrAt.public_eq_1]; rw [h1p]; rfl
      have ha2Eq : vcAttrAt (v 2).attrShares p.1 = vcExpectedDisclosedShare 2 p.2 := by
        rw [vcAttrAt.public_eq_1]; rw [h2p]; rfl
      simp only [vcSum3.public_eq_1]
      rw [ha0Eq, ha1Eq, ha2Eq]
      dsimp only [vcExpectedDisclosedShare, ↓reduceIte]
      have h10 : (1 : Fin 3) ≠ 0 := by decide
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      simp only [h10, h20, ↓reduceIte]
      rw [← goldOfInt_nat p.2, ← goldOfInt_nat Goldilocks.zero]
      simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1
    · unfold computeVcPoseidon2Commit
      rw [ite_true_of hAttrsLen]
      have hCS := hChunksSum (fun i => (v i).holderBlindShare) vcAttrCommitTag
      dsimp only at hCS
      rw [← hCS]
      dsimp only
      rw [← hLeafSum]
    · rw [← hEvalBool, ← hRootMerkleSum, ← hRootEq, hAccSum]
    · unfold computeVcPoseidon2Commit
      rw [ite_true_of hAttrsLen]
      have hCS := hChunksSum (fun i => (v i).presBlindShare) vcPresCommitTag
      dsimp only at hCS
      rw [← hCS]
      dsimp only
      rw [← hPresSpongeSum, ← hPresEq, hPresSum]
    · rw [computeVcScopeTag.public_eq_1]
      have hSC := hScopeChunksSum
      dsimp only at hSC
      rw [← hSC]
      dsimp only
      rw [← hScopeSpongeSum, ← hScopeEq, hScSum]

theorem verifyOpenedBlindVcRep_extract3_from_rewound
    {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {presNonce : Vec UInt8 32} {schema : VcSchema} {issuerEpoch : UInt64} {treeDepth : Nat}
    {accRoot presCommit scopeTag : Lane6} {verifierScopeLimbs : Lane4}
    {disclosed : List (Nat × Goldilocks)} {repIdx : Nat}
    {o0 o1 o2 : OpenedBlindVcRep}
    (hR1_01 : reconstructRepRound1 H presNonce repIdx o0 = reconstructRepRound1 H presNonce repIdx o1)
    (hR1_12 : reconstructRepRound1 H presNonce repIdx o1 = reconstructRepRound1 H presNonce repIdx o2)
    (hVer0 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 0 o0 = true)
    (hVer1 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 1 o1 = true)
    (hVer2 : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
      accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 2 o2 = true) :
    (∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂) ∨
    ∃ (attrs : List Goldilocks) (holderBlind presBlind : Lane4)
      (leafCommit : Lane6) (boolSteps : List (Bool × Lane6)),
      (disclosed.map Prod.fst).Nodup ∧
      attrs.length = schema.arity ∧
      (∀ p ∈ disclosed, p.1 < schema.arity ∧ attrs[p.1]? = some p.2) ∧
      computeVcPoseidon2Commit schema attrs holderBlind vcAttrCommitTag = some leafCommit ∧
      boolSteps.length = treeDepth ∧
      evalVcMerklePathBool issuerEpoch 0 leafCommit boolSteps = accRoot ∧
      computeVcPoseidon2Commit schema attrs presBlind vcPresCommitTag = some presCommit ∧
      computeVcScopeTag schema.schemaId holderBlind verifierScopeLimbs = scopeTag := by
  rcases verifyOpenedBlindVcRep_extract3_finite_conflict hR1_01 hR1_12 hVer0 hVer1 hVer2 with h | h
  · exact Or.inl (vcRewoundCommitConflict_hash_collision hHLen h)
  · exact Or.inr h

/-- An accepted opened repetition checked the disclosed-index list of the statement. -/
theorem verifyOpenedBlindVcRep_disclosedStrictAsc
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {schema : VcSchema} {issuerEpoch : UInt64} {treeDepth : Nat}
    {accRoot presCommit scopeTag : Lane6} {verifierScopeLimbs : Lane4}
    {disclosed : List (Nat × Goldilocks)} {repIdx : Nat} {expectedE : Fin 3}
    {o : OpenedBlindVcRep}
    (h : verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth accRoot presCommit scopeTag
      verifierScopeLimbs disclosed repIdx expectedE o = true) :
    vcCheckDisclosedStrictAsc schema.arity disclosed = true := by
  unfold verifyOpenedBlindVcRep at h; dsimp only at h
  cases hG :
      (decide (o.e = expectedE) &&
       vcCheckDisclosedStrictAsc schema.arity disclosed &&
       decide (o.viewE.attrShares.length = schema.arity) &&
       decide (o.viewE1.attrShares.length = schema.arity) &&
       decide (o.viewE.merkleLevels.length = treeDepth) &&
       decide (o.viewE1.merkleLevels.length = treeDepth) &&
       vcCheckPartyDisclosedShares o.e o.viewE.attrShares disclosed &&
       vcCheckPartyDisclosedShares (vcNextParty3 o.e) o.viewE1.attrShares disclosed &&
       checkPartyPrgTape prgExpand treeDepth repIdx o.e o.viewE &&
       checkPartyPrgTape prgExpand treeDepth repIdx (vcNextParty3 o.e) o.viewE1) with
  | false => rw [hG] at h; cases h
  | true => simp only [Bool.and_eq_true] at hG; exact hG.1.1.1.1.1.1.1.1.2

/-- The three openings of one honest repetition agree on every overlapping view. -/
theorem vcRewoundCommitConflict_honest_table
    (H : List UInt8 → List UInt8) (nonce : Vec UInt8 32) (idx : Nat)
    (tr : BlindVcRepTriple) :
    ¬ VcRewoundCommitConflict H nonce idx
      (openBlindVcRep H nonce idx tr 0)
      (openBlindVcRep H nonce idx tr 1)
      (openBlindVcRep H nonce idx tr 2) := by
  simp only [VcRewoundCommitConflict, openBlindVcRep, vcNextParty3,
    ne_eq, not_true_eq_false, false_and, or_self, not_false_eq_true]

/-- Bitwise `UInt8` XOR helpers (`0` `ofReduceBool`, `0 Classical.choice`). -/
private theorem uint8_xor_self_left (b m : UInt8) : b ^^^ (b ^^^ m) = m := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
  cases b.toBitVec.getLsbD i <;> cases m.toBitVec.getLsbD i <;> rfl

private theorem uint8_xor_zero_right (b : UInt8) : b ^^^ 0 = b := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
  rw [show (0 : UInt8).toBitVec = 0#8 from rfl, BitVec.getLsbD_zero]
  cases b.toBitVec.getLsbD i <;> rfl

def xorBytesWithVec : {n : Nat} → List UInt8 → Vec UInt8 n → Vec UInt8 n
  | 0, _, .nil => .nil
  | _ + 1, [], .cons m ms => .cons m (xorBytesWithVec [] ms)
  | _ + 1, b :: bs, .cons m ms => .cons (b ^^^ m) (xorBytesWithVec bs ms)

theorem xorBytesWithVec_involutive :
    ∀ {n : Nat} (bs : List UInt8) (v : Vec UInt8 n),
      xorBytesWithVec bs (xorBytesWithVec bs v) = v
  | 0, _, .nil => rfl
  | _ + 1, [], .cons m ms => by
    simp only [xorBytesWithVec]
    rw [xorBytesWithVec_involutive [] ms]
  | _ + 1, b :: bs, .cons m ms => by
    simp only [xorBytesWithVec]
    rw [uint8_xor_self_left, xorBytesWithVec_involutive bs ms]

private theorem xorBytesWithVec_zero_toList :
    ∀ {n : Nat} {bs : List UInt8},
      bs.length = n →
      (xorBytesWithVec bs (Vec.replicate n 0)).toList = bs
  | 0, [], _ => rfl
  | n + 1, b :: bs, hLen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [Vec.replicate, xorBytesWithVec, Vec.toList]
    rw [uint8_xor_zero_right, xorBytesWithVec_zero_toList hLen]

def xorBytesWithVecEquiv {n : Nat} (bs : List UInt8) : SimpleEquiv (Vec UInt8 n) (Vec UInt8 n) where
  toFun v := xorBytesWithVec bs v
  invFun v := xorBytesWithVec bs v
  left_inv := xorBytesWithVec_involutive bs
  right_inv := xorBytesWithVec_involutive bs


/-- Attribute slot sharing: pins disclosed slots to `(val, 0, 0)` and secret-shares undisclosed slots. -/
def vcShareAttrs3 (disclosed : List (Nat × Goldilocks)) :
    {n : Nat} → Nat → Vec Goldilocks n → Vec (Goldilocks × Goldilocks) n → Fin 3 → List Goldilocks
  | 0, _, .nil, .nil, _ => []
  | _ + 1, slot, .cons a as, .cons c cs, i =>
    let headShare :=
      match vcLookupDisclosed disclosed slot with
      | some _ => vcConstWire3 a i
      | none => vcShareWire3 a c i
    headShare :: vcShareAttrs3 disclosed (slot + 1) as cs i

/-- Simulator attribute-pair builder (ZERO secret witness inputs!). -/
def simAttrPairs (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    {n : Nat} → Nat → Vec (Goldilocks × Goldilocks) n → List Goldilocks × List Goldilocks
  | 0, _, .nil => ([], [])
  | _ + 1, slot, .cons p ps =>
    let hp :=
      match vcLookupDisclosed disclosed slot with
      | some pubVal => vcConstPair e pubVal
      | none => p
    let tp := simAttrPairs e disclosed (slot + 1) ps
    (hp.1 :: tp.1, hp.2 :: tp.2)

def vcAttrSharesEquiv3 (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    {n : Nat} → Nat → Vec Goldilocks n →
    SimpleEquiv (Vec (Goldilocks × Goldilocks) n) (Vec (Goldilocks × Goldilocks) n)
  | 0, _, .nil => seRefl _
  | _ + 1, slot, .cons a as =>
    let headEq :=
      match vcLookupDisclosed disclosed slot with
      | some _ => seRefl (Goldilocks × Goldilocks)
      | none => vcOpenedShareEquiv3 e a
    seDepCons headEq (fun _ => vcAttrSharesEquiv3 e disclosed (slot + 1) as)

theorem simAttrPairs_length (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (ps : Vec (Goldilocks × Goldilocks) n),
      (simAttrPairs e disclosed slot ps).1.length = n ∧
      (simAttrPairs e disclosed slot ps).2.length = n
  | 0, _, .nil => ⟨rfl, rfl⟩
  | _ + 1, slot, .cons _ ps => by
    obtain ⟨h1, h2⟩ := simAttrPairs_length e disclosed (slot + 1) ps
    simp only [simAttrPairs, List.length_cons]
    exact ⟨by omega, by omega⟩

private theorem simAttrPairs_getElem? (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (ps : Vec (Goldilocks × Goldilocks) n) (k : Nat) (hk : k < n),
      ((simAttrPairs e disclosed slot ps).1[k]?, (simAttrPairs e disclosed slot ps).2[k]?) =
        match vcLookupDisclosed disclosed (slot + k) with
        | some pubVal => (some (vcConstPair e pubVal).1, some (vcConstPair e pubVal).2)
        | none => (some (ps.toList[k]'(by rw [Vec.toList_length]; exact hk)).1,
                   some (ps.toList[k]'(by rw [Vec.toList_length]; exact hk)).2)
  | 0, _, .nil, _, hk => nomatch hk
  | _ + 1, slot, .cons p ps, 0, _ => by
    simp only [simAttrPairs, Vec.toList, List.getElem?_cons_zero, List.getElem_cons_zero, Nat.add_zero]
    cases vcLookupDisclosed disclosed slot <;> rfl
  | _ + 1, slot, .cons p ps, k + 1, hk => by
    have hk' : k < _ := Nat.lt_of_succ_lt_succ hk
    simp only [simAttrPairs, Vec.toList, List.getElem?_cons_succ, List.getElem_cons_succ]
    rw [simAttrPairs_getElem? e disclosed (slot + 1) ps k hk']
    have hSlot : slot + 1 + k = slot + (k + 1) := by omega
    simp only [hSlot]

theorem simAttrPairs_disclosed_ok (e : Fin 3) {arity : Nat} {disclosed : List (Nat × Goldilocks)}
    (hAsc : vcCheckDisclosedStrictAsc arity disclosed = true)
    (ps : Vec (Goldilocks × Goldilocks) arity) :
    vcCheckPartyDisclosedShares e (simAttrPairs e disclosed 0 ps).1 disclosed = true ∧
    vcCheckPartyDisclosedShares (vcNextParty3 e) (simAttrPairs e disclosed 0 ps).2 disclosed = true := by
  obtain ⟨hBounds, hNodup⟩ := vcCheckDisclosedStrictAsc_bounds_and_nodup hAsc
  have hAt : ∀ idx val, (idx, val) ∈ disclosed →
      (simAttrPairs e disclosed 0 ps).1[idx]? = some (vcExpectedDisclosedShare e val) ∧
      (simAttrPairs e disclosed 0 ps).2[idx]? = some (vcExpectedDisclosedShare (vcNextParty3 e) val) := by
    intro idx val hMem
    have hLt : idx < arity := hBounds (idx, val) hMem
    have hLook : vcLookupDisclosed disclosed idx = some val := vcLookupDisclosed_eq_some_of_nodup hNodup hMem
    have hGet := simAttrPairs_getElem? e disclosed 0 ps idx hLt
    rw [Nat.zero_add, hLook] at hGet
    dsimp only at hGet
    rw [vcConstPair_spec val e] at hGet
    injection hGet with h1 h2
    exact ⟨h1, h2⟩
  have hLoop : ∀ sub : List (Nat × Goldilocks),
      (∀ p ∈ sub, p ∈ disclosed) →
      vcCheckPartyDisclosedShares e (simAttrPairs e disclosed 0 ps).1 sub = true ∧
      vcCheckPartyDisclosedShares (vcNextParty3 e) (simAttrPairs e disclosed 0 ps).2 sub = true := by
    intro sub hSub
    induction sub with
    | nil => exact ⟨rfl, rfl⟩
    | cons hd tl ih =>
      rcases hd with ⟨idx, val⟩
      obtain ⟨h1, h2⟩ := hAt idx val (hSub (idx, val) (.head tl))
      obtain ⟨ih1, ih2⟩ := ih (fun q hq => hSub q (.tail _ hq))
      refine ⟨?_, ?_⟩
      · simp only [vcCheckPartyDisclosedShares, h1, ih1, decide_true, Bool.and_self]
      · simp only [vcCheckPartyDisclosedShares, h2, ih2, decide_true, Bool.and_self]
  exact hLoop disclosed (fun _ hp => hp)

theorem simAttrPairs_eq_honest (e : Fin 3) (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (attrs : Vec Goldilocks n) (coins : Vec (Goldilocks × Goldilocks) n),
      (∀ k : Nat, (hk : k < n) → ∀ pubVal, vcLookupDisclosed disclosed (slot + k) = some pubVal →
        attrs.toList[k]'(by rw [Vec.toList_length]; exact hk) = pubVal) →
      simAttrPairs e disclosed slot ((vcAttrSharesEquiv3 e disclosed slot attrs).toFun coins) =
        (vcShareAttrs3 disclosed slot attrs coins e,
         vcShareAttrs3 disclosed slot attrs coins (vcNextParty3 e))
  | 0, _, .nil, .nil, _ => rfl
  | _ + 1, slot, .cons a as, .cons c cs, hPin => by
    simp only [vcAttrSharesEquiv3, seDepCons, seDepConsToFun, simAttrPairs, vcShareAttrs3]
    have hTail := simAttrPairs_eq_honest e disclosed (slot + 1) as cs (fun k hk pv hL => by
      have hSlot : slot + 1 + k = slot + (k + 1) := by omega
      rw [hSlot] at hL
      exact hPin (k + 1) (Nat.succ_lt_succ hk) pv hL)
    rw [hTail]
    cases hLook : vcLookupDisclosed disclosed slot with
    | none =>
      simp only [vcOpenedShareEquiv3_toFun, vcPairAt]
    | some pubVal =>
      have haEq : a = pubVal := by
        have h0 := hPin 0 (Nat.zero_lt_succ _) pubVal (by rw [Nat.add_zero]; exact hLook)
        simpa [Vec.toList] using h0
      rw [haEq]
      dsimp only [seRefl]
      rw [vcConstPair_spec pubVal e]
      rfl

private theorem vcShareAttrs3_length (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (attrs : Vec Goldilocks n) (coins : Vec (Goldilocks × Goldilocks) n) (i : Fin 3),
      (vcShareAttrs3 disclosed slot attrs coins i).length = n
  | 0, _, .nil, .nil, _ => rfl
  | _ + 1, slot, .cons _ as, .cons _ cs, i => by
    simp only [vcShareAttrs3, List.length_cons]
    rw [vcShareAttrs3_length disclosed (slot + 1) as cs i]

theorem vcShareAttrs3_sum_getElem? (disclosed : List (Nat × Goldilocks)) :
    ∀ {n : Nat} (slot : Nat) (attrs : Vec Goldilocks n) (coins : Vec (Goldilocks × Goldilocks) n) (k : Nat),
      vcSum3 (fun i => vcAttrAt (vcShareAttrs3 disclosed slot attrs coins i) k) =
        vcAttrAt attrs.toList k
  | 0, _, .nil, .nil, k => by
    simp only [vcAttrAt.public_eq_1]
    simp only [vcShareAttrs3, Vec.toList, List.getElem?_nil, Option.getD]
    exact vcSum3_zero
  | _ + 1, slot, .cons a as, .cons c cs, 0 => by
    simp only [vcAttrAt.public_eq_1]
    simp only [vcShareAttrs3, Vec.toList, List.getElem?_cons_zero, Option.getD]
    cases vcLookupDisclosed disclosed slot with
    | some _ => exact vcSum3_constWire a
    | none => exact vcSum3_shareWire3 a c
  | _ + 1, slot, .cons _ as, .cons _ cs, k + 1 => by
    have ih := vcShareAttrs3_sum_getElem? disclosed (slot + 1) as cs k
    simp only [vcAttrAt.public_eq_1] at ih ⊢
    simp only [vcShareAttrs3, Vec.toList, List.getElem?_cons_succ]
    exact ih

/-! #### Public Statement, Secret Witness, Full `OpenedBlindVcRep` Simulator & `zkMultiRepViewEquiv` -/

/-- Public statement for `BlindVC` selective disclosure. -/
structure BlindVcPublicStatement where
  schema : VcSchema
  treeDepth : Nat
  presNonce : Vec UInt8 32
  issuerEpoch : UInt64
  accumulatorRoot : Lane6
  presCommit : Lane6
  scopeTag : Lane6
  verifierScopeLimbs : Lane4
  disclosedAttrs : List (Nat × Goldilocks)

/-- Holder's secret credential + boolean Merkle accumulator witness. -/
structure BlindVcSecretWitness (arity treeDepth : Nat) where
  attrs : Vec Goldilocks arity
  holderBlind : Lane4
  presBlind : Lane4
  merkleSteps : Vec (Bool × Lane6) treeDepth

/-- Validity relation connecting `BlindVcSecretWitness` to `BlindVcPublicStatement`. -/
def BlindVcWitnessValid (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth) : Prop :=
  vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true ∧
  (∀ p ∈ stmt.disclosedAttrs, wit.attrs.toList[p.1]? = some p.2) ∧
  (∃ leaf : Lane6,
    computeVcPoseidon2Commit stmt.schema wit.attrs.toList wit.holderBlind vcAttrCommitTag = some leaf ∧
    evalVcMerklePathBool stmt.issuerEpoch 0 leaf wit.merkleSteps.toList = stmt.accumulatorRoot) ∧
  computeVcPoseidon2Commit stmt.schema wit.attrs.toList wit.presBlind vcPresCommitTag = some stmt.presCommit ∧
  computeVcScopeTag stmt.schema.schemaId wit.holderBlind stmt.verifierScopeLimbs = stmt.scopeTag

/-- Per-repetition randomness space shared by Hybrid-1 honest execution and the zero-knowledge simulator. -/
structure RepRandomness (arity treeDepth : Nat) where
  seedE : Vec UInt8 32
  seedE1 : Vec UInt8 32
  saltE : Vec UInt8 32
  saltE1 : Vec UInt8 32
  attrShareCoins : Vec (Goldilocks × Goldilocks) arity
  holderBlindCoins : Lane4 × Lane4
  presBlindCoins : Lane4 × Lane4
  merkleStepCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) treeDepth
  gateCoins : PartyGateCoins treeDepth
  unopenedCommitCoins : Vec UInt8 32

private def partyGateCoinsTupleEquiv {D : Nat} :
    SimpleEquiv (PartyGateCoins D)
      (Sponge3Coins × Sponge3Coins × Sponge3Coins × Vec MerkleLevelCoins D) where
  toFun g := (g.attrCoins, g.presCoins, g.scopeCoins, g.merkleCoins)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv := fun ⟨_, _, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _, _⟩ => rfl

/-- Constructive 3-share output completion from public `target` and opened `(sE, sE1)`. -/
def completeLane6Shares3 (e : Fin 3) (target : Lane6) (pair : Lane6 × Lane6) : Triple3 Lane6 :=
  Triple3.ofFn (mkParty3At e pair.1 pair.2 (lane6Sub (lane6Sub target pair.1) pair.2))

def completeZeroShares3 (e : Fin 3) (pairs : List (Goldilocks × Goldilocks)) : List (Triple3 Goldilocks) :=
  pairs.map (fun p => Triple3.ofFn (mkParty3At e p.1 p.2 (Goldilocks.sub (Goldilocks.sub Goldilocks.zero p.1) p.2)))

/-- **Zero-Knowledge Simulator (`simulateOpenedBlindVcRep`)**:
    Takes **ONLY** the public statement `stmt`, repetition index `repIdx`, challenge `e`, and
    uniform `simRand : RepRandomness` (**ZERO** secret witness arguments!), expands real PRG tapes
    from `(seedE, seedE1)`, and produces a complete `OpenedBlindVcRep` (`viewE`, `viewE1`,
    `unopenedCommit`, `finalOuts`). -/
def simulateOpenedBlindVcRep
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement) (repIdx : Nat) (e : Fin 3)
    (simRand : RepRandomness stmt.schema.arity stmt.treeDepth) : OpenedBlindVcRep :=
  let e1 := vcNextParty3 e
  let gE := prgExpand stmt.treeDepth repIdx e simRand.seedE
  let gE1 := prgExpand stmt.treeDepth repIdx e1 simRand.seedE1
  let (attrsE, attrsE1) := simAttrPairs e stmt.disclosedAttrs 0 simRand.attrShareCoins
  let (hbE, hbE1) := simRand.holderBlindCoins
  let (pbE, pbE1) := simRand.presBlindCoins
  let (ac0, ac1, ac2) := vcPairCommitChunks e stmt.schema attrsE attrsE1 hbE hbE1 vcAttrCommitTag
  let (pc0, pc1, pc2) := vcPairCommitChunks e stmt.schema attrsE attrsE1 pbE pbE1 vcPresCommitTag
  let (sc0, sc1, sc2) := vcPairScopeChunks e stmt.schema.schemaId hbE hbE1 stmt.verifierScopeLimbs
  let attrSim := simSponge3Perm e ac0 ac1 ac2 gE.attrCoins gE1.attrCoins simRand.gateCoins.attrCoins
  let presSim := simSponge3Perm e pc0 pc1 pc2 gE.presCoins gE1.presCoins simRand.gateCoins.presCoins
  let scopeSim := simSponge3Perm e sc0 sc1 sc2 gE.scopeCoins gE1.scopeCoins simRand.gateCoins.scopeCoins
  let mkSim := simMerklePath e stmt.issuerEpoch 0 attrSim.2 simRand.merkleStepCoins
    gE.merkleCoins gE1.merkleCoins simRand.gateCoins.merkleCoins
  let viewE : PartyVcRepView :=
    { tapeSeed := simRand.seedE
      commitSalt := simRand.saltE
      attrShares := attrsE
      holderBlindShare := hbE
      presBlindShare := pbE
      attrSponge := attrSim.1.1
      merkleLevels := mkSim.1.1
      presSponge := presSim.1.1
      scopeSponge := scopeSim.1.1 }
  let viewE1 : PartyVcRepView :=
    { tapeSeed := simRand.seedE1
      commitSalt := simRand.saltE1
      attrShares := attrsE1
      holderBlindShare := hbE1
      presBlindShare := pbE1
      attrSponge := attrSim.1.2
      merkleLevels := mkSim.1.2
      presSponge := presSim.1.2
      scopeSponge := scopeSim.1.2 }
  let finalOuts : VcRepFinalOuts3 :=
    { rootShares := completeLane6Shares3 e stmt.accumulatorRoot mkSim.2.1
      presShares := completeLane6Shares3 e stmt.presCommit presSim.2
      scopeShares := completeLane6Shares3 e stmt.scopeTag scopeSim.2
      boolZeroShares := completeZeroShares3 e mkSim.2.2 }
  { e := e
    viewE := viewE
    viewE1 := viewE1
    unopenedCommit := simRand.unopenedCommitCoins.toList
    finalOuts := finalOuts }

/-- Build a full 3-party `BlindVcRepTriple` from 3 party coin tapes `(g 0, g 1, g 2)`. -/
def buildHonestBlindVcTriple
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth)
    (gateCoins3 : Fin 3 → PartyGateCoins stmt.treeDepth) : BlindVcRepTriple :=
  let attrShares := vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins
  let hbShares := vcShareLane4_3 wit.holderBlind hbCoins
  let pbShares := vcShareLane4_3 wit.presBlind pbCoins
  let mkSteps3 := vcShareMerkleSteps3 wit.merkleSteps mkCoins
  let (ac0, ac1, ac2) := vcCommitChunks3 stmt.schema attrShares hbShares vcAttrCommitTag
  let (pc0, pc1, pc2) := vcCommitChunks3 stmt.schema attrShares pbShares vcPresCommitTag
  let (sc0, sc1, sc2) := vcScopeChunks3 stmt.schema.schemaId hbShares stmt.verifierScopeLimbs
  let attrRun := honestSponge3Perm3 ac0 ac1 ac2 (fun i => (gateCoins3 i).attrCoins)
  let presRun := honestSponge3Perm3 pc0 pc1 pc2 (fun i => (gateCoins3 i).presCoins)
  let scopeRun := honestSponge3Perm3 sc0 sc1 sc2 (fun i => (gateCoins3 i).scopeCoins)
  let mkRun := honestMerklePath3 stmt.issuerEpoch 0 attrRun.2 mkSteps3 (fun i => (gateCoins3 i).merkleCoins)
  { views := fun i =>
      { tapeSeed := seeds i
        commitSalt := salts i
        attrShares := attrShares i
        holderBlindShare := hbShares i
        presBlindShare := pbShares i
        attrSponge := attrRun.1 i
        merkleLevels := mkRun.1 i
        presSponge := presRun.1 i
        scopeSponge := scopeRun.1 i }
    finalOuts :=
      { rootShares := Triple3.ofFn mkRun.2.1
        presShares := Triple3.ofFn presRun.2
        scopeShares := Triple3.ofFn scopeRun.2
        boolZeroShares := mkRun.2.2.map Triple3.ofFn } }

/-- Hybrid-1 honest repetition opening (`[GMO16, Lemma 4.2]`):
    opened parties `e` and `(e+1)%3` expand real PRG tapes `prgExpand ... seedE` and `prgExpand ... seedE1`
    and real salted commitments, while the unopened 3rd party `(e+2)%3` uses uniform gate coins
    `hRand.gateCoins` and XOR-masked commitment `hRand.unopenedCommitCoins`. -/
def honestHybrid1Rep
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (repIdx : Nat) (e : Fin 3)
    (hRand : RepRandomness stmt.schema.arity stmt.treeDepth) : OpenedBlindVcRep :=
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  let gE := prgExpand stmt.treeDepth repIdx e hRand.seedE
  let gE1 := prgExpand stmt.treeDepth repIdx e1 hRand.seedE1
  let seeds := mkParty3At e hRand.seedE hRand.seedE1 (Vec.replicate 32 0)
  let salts := mkParty3At e hRand.saltE hRand.saltE1 (Vec.replicate 32 0)
  let gateCoins3 := mkParty3At e gE gE1 hRand.gateCoins
  let triple := buildHonestBlindVcTriple stmt wit seeds salts
    hRand.attrShareCoins hRand.holderBlindCoins hRand.presBlindCoins hRand.merkleStepCoins gateCoins3
  let rawComU := vcCommitPartyView H stmt.presNonce repIdx e2 (triple.views e2)
    (vcPartyFinalOutAt triple.finalOuts e2)
  { e := e
    viewE := triple.views e
    viewE1 := triple.views e1
    unopenedCommit := (xorBytesWithVec rawComU hRand.unopenedCommitCoins).toList
    finalOuts := triple.finalOuts }

/-- Real-world PRG prover triple (`Hybrid 0`) from 3 `(tapeSeed, commitSalt)` pairs:
    opening `honestPrgTriple` at `e` is literally `honestHybrid1Rep` at
    `gateCoins := prgExpand ... seedU` and `unopenedCommitCoins := Vec.replicate 32 0`! -/
def honestPrgTriple
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (repIdx : Nat)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth) :
    BlindVcRepTriple :=
  buildHonestBlindVcTriple stmt wit seeds salts attrCoins hbCoins pbCoins mkCoins
    (fun i => prgExpand stmt.treeDepth repIdx i (seeds i))

private theorem buildHonestBlindVcTriple_sums
    {stmt : BlindVcPublicStatement}
    {wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth}
    (hValid : BlindVcWitnessValid stmt wit)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth)
    (gateCoins3 : Fin 3 → PartyGateCoins stmt.treeDepth) :
    let tr := buildHonestBlindVcTriple stmt wit seeds salts attrCoins hbCoins pbCoins mkCoins gateCoins3
    vcSumLane6_3 tr.finalOuts.rootShares.get = stmt.accumulatorRoot ∧
    vcSumLane6_3 tr.finalOuts.presShares.get = stmt.presCommit ∧
    vcSumLane6_3 tr.finalOuts.scopeShares.get = stmt.scopeTag ∧
    (∀ t ∈ tr.finalOuts.boolZeroShares, vcSum3 t.get = Goldilocks.zero) := by
  rcases hValid with ⟨_, _, ⟨leaf, hAttrCom, hMkEval⟩, hPresCom, hScopeEval⟩
  unfold buildHonestBlindVcTriple
  dsimp only
  have hGetFn : ∀ {α : Type} (f : Fin 3 → α), (Triple3.ofFn f).get = f :=
    fun f => funext (Triple3.get_ofFn f)
  rw [hGetFn, hGetFn, hGetFn]
  have hAttrsLen : wit.attrs.toList.length = stmt.schema.arity := Vec.toList_length wit.attrs
  unfold computeVcPoseidon2Commit at hAttrCom hPresCom
  rw [ite_true_of hAttrsLen] at hAttrCom hPresCom
  injection hAttrCom with hLeafEq
  injection hPresCom with hPresEq
  have hChunksEq : ∀ (blind : Lane4) (bCoins : Lane4 × Lane4) (tag : UInt64),
      let (c0, c1, c2) := vcCommitChunks3 stmt.schema
        (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins)
        (vcShareLane4_3 blind bCoins) tag
      (vcSumLane6_3 c0, vcSumLane6_3 c1, vcSumLane6_3 c2) =
        vcCommitChunks stmt.schema wit.attrs.toList blind tag := by
    intro blind bCoins tag
    unfold vcCommitChunks3
    rw [vcCommitChunks.public_eq_1]
    simp only [vcShareLane4_3.public_eq_1]
    simp only [vcSumLane6_3_eq, vcSum3_constWire, vcSum3_zero,
      vcShareAttrs3_sum_getElem?, vcSum3_shareWire3]
  have hAC := hChunksEq wit.holderBlind hbCoins vcAttrCommitTag
  dsimp only at hAC
  have hac0 := congrArg Prod.fst hAC
  have hac1 := congrArg (fun p => p.2.1) hAC
  have hac2 := congrArg (fun p => p.2.2) hAC
  dsimp only at hac0 hac1 hac2
  have hPC := hChunksEq wit.presBlind pbCoins vcPresCommitTag
  dsimp only at hPC
  have hpc0 := congrArg Prod.fst hPC
  have hpc1 := congrArg (fun p => p.2.1) hPC
  have hpc2 := congrArg (fun p => p.2.2) hPC
  dsimp only at hpc0 hpc1 hpc2
  have hSC :
      let (c0, c1, c2) := vcScopeChunks3 stmt.schema.schemaId
        (vcShareLane4_3 wit.holderBlind hbCoins) stmt.verifierScopeLimbs
      (vcSumLane6_3 c0, vcSumLane6_3 c1, vcSumLane6_3 c2) =
        vcScopeChunks stmt.schema.schemaId wit.holderBlind stmt.verifierScopeLimbs := by
    unfold vcScopeChunks3
    rw [vcScopeChunks.public_eq_1]
    simp only [vcShareLane4_3.public_eq_1]
    simp only [vcSumLane6_3_eq, vcSum3_constWire, vcSum3_zero, vcSum3_shareWire3]
  dsimp only at hSC
  have hsc0 := congrArg Prod.fst hSC
  have hsc1 := congrArg (fun p => p.2.1) hSC
  have hsc2 := congrArg (fun p => p.2.2) hSC
  dsimp only at hsc0 hsc1 hsc2
  let ac := vcCommitChunks3 stmt.schema
    (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins)
    (vcShareLane4_3 wit.holderBlind hbCoins) vcAttrCommitTag
  let pc := vcCommitChunks3 stmt.schema
    (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins)
    (vcShareLane4_3 wit.presBlind pbCoins) vcPresCommitTag
  let sc := vcScopeChunks3 stmt.schema.schemaId
    (vcShareLane4_3 wit.holderBlind hbCoins) stmt.verifierScopeLimbs
  have hAttrSum : vcSumLane6_3 (honestSponge3Perm3 ac.1 ac.2.1 ac.2.2 (fun i => (gateCoins3 i).attrCoins)).2 = leaf := by
    rw [honestSponge3Perm3_sum, hac0, hac1, hac2]; exact hLeafEq
  have hPresSum : vcSumLane6_3 (honestSponge3Perm3 pc.1 pc.2.1 pc.2.2 (fun i => (gateCoins3 i).presCoins)).2 = stmt.presCommit := by
    rw [honestSponge3Perm3_sum, hpc0, hpc1, hpc2]; exact hPresEq
  have hScopeSum : vcSumLane6_3 (honestSponge3Perm3 sc.1 sc.2.1 sc.2.2 (fun i => (gateCoins3 i).scopeCoins)).2 = stmt.scopeTag := by
    rw [honestSponge3Perm3_sum, hsc0, hsc1, hsc2]
    simpa only [computeVcScopeTag.public_eq_1] using hScopeEval
  obtain ⟨hMkRoot, hMkZeros⟩ := vcMerkleStepSum_bool stmt.issuerEpoch 0
    (honestSponge3Perm3 ac.1 ac.2.1 ac.2.2 (fun i => (gateCoins3 i).attrCoins)).2
    wit.merkleSteps mkCoins (fun i => (gateCoins3 i).merkleCoins)
  rw [hAttrSum, hMkEval] at hMkRoot
  refine ⟨hMkRoot, hPresSum, hScopeSum, ?_⟩
  intro t ht
  obtain ⟨z, hzMem, rfl⟩ := List.mem_map.mp ht
  rw [hGetFn]
  exact hMkZeros z hzMem

/-- Bijection on `PartyGateCoins` mapping unopened party coins `gU` to simulated `gateOutsE1`. -/
def partyGateOutEquiv (e : Fin 3) (stmt : BlindVcPublicStatement)
    (attrShares : Fin 3 → List Goldilocks)
    (hbShares pbShares : VcLane4_3)
    (mkSteps3 : Vec (VcWire3 × VcLane6_3) stmt.treeDepth)
    (gE gE1 : PartyGateCoins stmt.treeDepth) :
    SimpleEquiv (PartyGateCoins stmt.treeDepth) (PartyGateCoins stmt.treeDepth) :=
  let (ac0, ac1, ac2) := vcCommitChunks3 stmt.schema attrShares hbShares vcAttrCommitTag
  let (pc0, pc1, pc2) := vcCommitChunks3 stmt.schema attrShares pbShares vcPresCommitTag
  let (sc0, sc1, sc2) := vcScopeChunks3 stmt.schema.schemaId hbShares stmt.verifierScopeLimbs
  seTrans partyGateCoinsTupleEquiv
    (seTrans
      (seDepProd (sponge3OutEquiv e ac0 ac1 ac2 gE.attrCoins gE1.attrCoins) fun acU =>
        let leaf3 := (honestSponge3Perm3 ac0 ac1 ac2 (mkParty3At e gE.attrCoins gE1.attrCoins acU)).2
        seProdCongr (sponge3OutEquiv e pc0 pc1 pc2 gE.presCoins gE1.presCoins)
          (seProdCongr (sponge3OutEquiv e sc0 sc1 sc2 gE.scopeCoins gE1.scopeCoins)
            (merklePathOutEquiv e stmt.issuerEpoch 0 leaf3 mkSteps3 gE.merkleCoins gE1.merkleCoins)))
      (seSymm partyGateCoinsTupleEquiv))

private def repRandomnessTupleEquiv {A D : Nat} :
    SimpleEquiv (RepRandomness A D)
      ((Vec UInt8 32 × Vec UInt8 32 × Vec UInt8 32 × Vec UInt8 32) ×
       ((Vec (Goldilocks × Goldilocks) A × (Lane4 × Lane4) × (Lane4 × Lane4) ×
         Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) D) ×
        (PartyGateCoins D × Vec UInt8 32))) where
  toFun r := ((r.seedE, r.seedE1, r.saltE, r.saltE1),
              ((r.attrShareCoins, r.holderBlindCoins, r.presBlindCoins, r.merkleStepCoins),
               (r.gateCoins, r.unopenedCommitCoins)))
  invFun t := ⟨t.1.1, t.1.2.1, t.1.2.2.1, t.1.2.2.2,
               t.2.1.1, t.2.1.2.1, t.2.1.2.2.1, t.2.1.2.2.2,
               t.2.2.1, t.2.2.2⟩
  left_inv := fun ⟨_, _, _, _, _, _, _, _, _, _⟩ => rfl
  right_inv := fun ⟨⟨_, _, _, _⟩, ⟨⟨_, _, _, _⟩, ⟨_, _⟩⟩⟩ => rfl

/-- **Full-Repetition Zero-Knowledge Bijection (`zkOpenedRepFullEquiv`, `0 Classical.choice`)**:
    Maps the prover's Hybrid-1 randomness space bijectively onto the simulator's randomness space
    such that `honestHybrid1Rep` and `simulateOpenedBlindVcRep` output the **EXACT SAME**
    `OpenedBlindVcRep` (`viewE`, `viewE1`, `unopenedCommit`, AND `finalOuts`)! -/
def zkOpenedRepFullEquiv
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (repIdx : Nat) (e : Fin 3) :
    SimpleEquiv (RepRandomness stmt.schema.arity stmt.treeDepth)
                (RepRandomness stmt.schema.arity stmt.treeDepth) :=
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  let inEq :=
    seProdCongr (vcAttrSharesEquiv3 e stmt.disclosedAttrs 0 wit.attrs)
      (seProdCongr (vcLane4OpenedShareEquiv3 e wit.holderBlind)
        (seProdCongr (vcLane4OpenedShareEquiv3 e wit.presBlind)
          (vcMerkleStepsEquiv3 e wit.merkleSteps)))
  seTrans repRandomnessTupleEquiv
    (seTrans
      (seDepProd (seRefl _) fun ⟨seedE, seedE1, saltE, saltE1⟩ =>
        let gE := prgExpand stmt.treeDepth repIdx e seedE
        let gE1 := prgExpand stmt.treeDepth repIdx e1 seedE1
        seDepProd inEq fun ⟨attrCoins, hbCoins, pbCoins, mkCoins⟩ =>
          let attrShares := vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrCoins
          let hbShares := vcShareLane4_3 wit.holderBlind hbCoins
          let pbShares := vcShareLane4_3 wit.presBlind pbCoins
          let mkSteps3 := vcShareMerkleSteps3 wit.merkleSteps mkCoins
          seDepProd (partyGateOutEquiv e stmt attrShares hbShares pbShares mkSteps3 gE gE1) fun gateU =>
            let seeds := mkParty3At e seedE seedE1 (Vec.replicate 32 0)
            let salts := mkParty3At e saltE saltE1 (Vec.replicate 32 0)
            let gateCoins3 := mkParty3At e gE gE1 gateU
            let triple := buildHonestBlindVcTriple stmt wit seeds salts attrCoins hbCoins pbCoins mkCoins gateCoins3
            let rawComU := vcCommitPartyView H stmt.presNonce repIdx e2 (triple.views e2)
              (vcPartyFinalOutAt triple.finalOuts e2)
            xorBytesWithVecEquiv rawComU)
      (seSymm repRandomnessTupleEquiv))

/-- **Exact Full-View Simulation Theorem (`zkOpenedRepFullEquiv_simulates`)**:
    For every valid secret witness `wit` and every randomness draw `hRand`,
    `honestHybrid1Rep` equals `simulateOpenedBlindVcRep` across ALL fields of `OpenedBlindVcRep`! -/
theorem zkOpenedRepFullEquiv_simulates
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (repIdx : Nat) (e : Fin 3)
    (hRand : RepRandomness stmt.schema.arity stmt.treeDepth) :
    honestHybrid1Rep H prgExpand stmt wit repIdx e hRand =
      simulateOpenedBlindVcRep prgExpand stmt repIdx e
        ((zkOpenedRepFullEquiv H prgExpand stmt wit repIdx e).toFun hRand) := by
  have hPin : ∀ k : Nat, (hk : k < stmt.schema.arity) → ∀ pubVal,
      vcLookupDisclosed stmt.disclosedAttrs (0 + k) = some pubVal →
      wit.attrs.toList[k]'(by rw [Vec.toList_length]; exact hk) = pubVal := by
    intro k hk pubVal hLook
    rw [Nat.zero_add] at hLook
    have hSome := hValid.2.1 (k, pubVal) (vcLookupDisclosed_mem hLook)
    rw [List.getElem?_eq_getElem (by rw [Vec.toList_length]; exact hk)] at hSome
    injection hSome
  obtain ⟨hRootSum, hPresSum, hScopeSum, hBoolZeros⟩ :=
    buildHonestBlindVcTriple_sums hValid
      (mkParty3At e hRand.seedE hRand.seedE1 (Vec.replicate 32 0))
      (mkParty3At e hRand.saltE hRand.saltE1 (Vec.replicate 32 0))
      hRand.attrShareCoins hRand.holderBlindCoins hRand.presBlindCoins hRand.merkleStepCoins
      (mkParty3At e (prgExpand stmt.treeDepth repIdx e hRand.seedE)
        (prgExpand stmt.treeDepth repIdx (vcNextParty3 e) hRand.seedE1) hRand.gateCoins)
  rcases hRand with ⟨seedE, seedE1, saltE, saltE1, attrC, hbC, pbC, mkC, gateU, comMask⟩
  let e1 := vcNextParty3 e
  let gE := prgExpand stmt.treeDepth repIdx e seedE
  let gE1 := prgExpand stmt.treeDepth repIdx e1 seedE1
  have hAttrSim : simAttrPairs e stmt.disclosedAttrs 0
      ((vcAttrSharesEquiv3 e stmt.disclosedAttrs 0 wit.attrs).1 attrC) =
      (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrC e,
       vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrC (vcNextParty3 e)) :=
    simAttrPairs_eq_honest e stmt.disclosedAttrs 0 wit.attrs attrC hPin
  have hHbFst : ((vcLane4OpenedShareEquiv3 e wit.holderBlind).toFun hbC).fst =
      vcShareLane4_3 wit.holderBlind hbC e :=
        congrArg Prod.fst (vcLane4OpenedShareEquiv3_toFun ..)
  have hHbSnd : ((vcLane4OpenedShareEquiv3 e wit.holderBlind).toFun hbC).snd =
      vcShareLane4_3 wit.holderBlind hbC (vcNextParty3 e) :=
        congrArg Prod.snd (vcLane4OpenedShareEquiv3_toFun ..)
  have hPbFst : ((vcLane4OpenedShareEquiv3 e wit.presBlind).toFun pbC).fst =
      vcShareLane4_3 wit.presBlind pbC e :=
        congrArg Prod.fst (vcLane4OpenedShareEquiv3_toFun ..)
  have hPbSnd : ((vcLane4OpenedShareEquiv3 e wit.presBlind).toFun pbC).snd =
      vcShareLane4_3 wit.presBlind pbC (vcNextParty3 e) :=
        congrArg Prod.snd (vcLane4OpenedShareEquiv3_toFun ..)
  unfold honestHybrid1Rep simulateOpenedBlindVcRep zkOpenedRepFullEquiv partyGateOutEquiv buildHonestBlindVcTriple
  dsimp only [seTrans, seDepProd, seProdCongr, seRefl,
    seSymm, repRandomnessTupleEquiv, partyGateCoinsTupleEquiv, xorBytesWithVecEquiv]
  rw [hAttrSim, hHbFst, hHbSnd, hPbFst, hPbSnd]
  dsimp only
  rw [vcPairCommitChunks_spec e stmt.schema
        (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrC)
        (vcShareLane4_3 wit.holderBlind hbC) vcAttrCommitTag,
      vcPairCommitChunks_spec e stmt.schema
        (vcShareAttrs3 stmt.disclosedAttrs 0 wit.attrs attrC)
        (vcShareLane4_3 wit.presBlind pbC) vcPresCommitTag,
      vcPairScopeChunks_spec e stmt.schema.schemaId
        (vcShareLane4_3 wit.holderBlind hbC) stmt.verifierScopeLimbs]
  dsimp only
  have hgAttr : (fun i => (mkParty3At e gE gE1 gateU i).attrCoins) =
      mkParty3At e gE.attrCoins gE1.attrCoins gateU.attrCoins := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hgPres : (fun i => (mkParty3At e gE gE1 gateU i).presCoins) =
      mkParty3At e gE.presCoins gE1.presCoins gateU.presCoins := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hgScope : (fun i => (mkParty3At e gE gE1 gateU i).scopeCoins) =
      mkParty3At e gE.scopeCoins gE1.scopeCoins gateU.scopeCoins := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  have hgMk : (fun i => (mkParty3At e gE gE1 gateU i).merkleCoins) =
      mkParty3At e gE.merkleCoins gE1.merkleCoins gateU.merkleCoins := by
    funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
  rw [hgAttr, hgPres, hgScope, hgMk]
  rw [simSponge3Perm_eq_honest, simSponge3Perm_eq_honest, simSponge3Perm_eq_honest]
  dsimp only
  rw [simMerklePath_eq_honest]
  dsimp only
  rw [mkParty3At_e, mkParty3At_next, mkParty3At_e, mkParty3At_next]
  congr 1
  unfold buildHonestBlindVcTriple at hRootSum hPresSum hScopeSum hBoolZeros
  dsimp only at hRootSum hPresSum hScopeSum hBoolZeros
  rw [hgAttr, hgMk] at hRootSum hBoolZeros
  rw [hgPres] at hPresSum
  rw [hgScope] at hScopeSum
  have hGetFn : ∀ {α : Type} (f : Fin 3 → α), (Triple3.ofFn f).get = f :=
    fun f => funext (Triple3.get_ofFn f)
  rw [hGetFn] at hRootSum hPresSum hScopeSum
  have hR := vcUnopened_of_sumLane6_3 e hRootSum
  have hP := vcUnopened_of_sumLane6_3 e hPresSum
  have hS := vcUnopened_of_sumLane6_3 e hScopeSum
  unfold completeLane6Shares3 completeZeroShares3 vcPairAtLane6
  congr 1
  · exact congrArg Triple3.ofFn hR
  · exact congrArg Triple3.ofFn hP
  · exact congrArg Triple3.ofFn hS
  · rw [List.map_map]
    have hMapEq : ∀ (bzs : List VcWire3),
        (∀ t ∈ List.map Triple3.ofFn bzs, vcSum3 t.get = Goldilocks.zero) →
        List.map Triple3.ofFn bzs =
          List.map ((fun p : Goldilocks × Goldilocks =>
            Triple3.ofFn (mkParty3At e p.1 p.2
              (Goldilocks.sub (Goldilocks.sub Goldilocks.zero p.1) p.2))) ∘
            (fun w => vcPairAt w e)) bzs := by
      intro bzs hBZ
      induction bzs with
      | nil => rfl
      | cons z zs ih =>
        dsimp only [List.map, Function.comp, vcPairAt]
        have hzSum : vcSum3 z = Goldilocks.zero := by
          have hm := hBZ (Triple3.ofFn z) (.head _)
          rwa [hGetFn] at hm
        have hz0 := vcUnopened_of_sum3 e hzSum
        rw [← congrArg Triple3.ofFn hz0, ih (fun t ht => hBZ t (.tail _ ht))]
        rfl
    exact hMapEq _ hBoolZeros

/-- Every simulated `OpenedBlindVcRep` passes `verifyOpenedBlindVcRep = true` (including
    `checkPartyPrgTape` on BOTH `viewE` and `viewE1`) whenever `stmt.disclosedAttrs` is strictly ascending. -/
theorem simulateOpenedBlindVcRep_verifies
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (hAsc : vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true)
    (repIdx : Nat) (e : Fin 3)
    (simRand : RepRandomness stmt.schema.arity stmt.treeDepth) :
    verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
      stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
      stmt.disclosedAttrs repIdx e (simulateOpenedBlindVcRep prgExpand stmt repIdx e simRand) = true := by
  let o := simulateOpenedBlindVcRep prgExpand stmt repIdx e simRand
  obtain ⟨hALen1, hALen2⟩ := simAttrPairs_length e stmt.disclosedAttrs 0 simRand.attrShareCoins
  obtain ⟨hDisc1, hDisc2⟩ := simAttrPairs_disclosed_ok e hAsc simRand.attrShareCoins
  let gE := prgExpand stmt.treeDepth repIdx e simRand.seedE
  let gE1 := prgExpand stmt.treeDepth repIdx (vcNextParty3 e) simRand.seedE1
  obtain ⟨hMkLen1, hMkLen2⟩ := simMerklePath_length e stmt.issuerEpoch 0 _ simRand.merkleStepCoins
    gE.merkleCoins gE1.merkleCoins simRand.gateCoins.merkleCoins
  have hTapeE : checkPartyPrgTape prgExpand stmt.treeDepth repIdx e o.viewE = true := by
    rw [checkPartyPrgTape.public_eq_1]
    apply decide_eq_true
    unfold extractPartyGateCoins
    dsimp only [o, simulateOpenedBlindVcRep]
    rw [(extractSponge3Coins_sim e _ _ _ gE.attrCoins gE1.attrCoins _).1,
        (extractSponge3Coins_sim e _ _ _ gE.presCoins gE1.presCoins _).1,
        (extractSponge3Coins_sim e _ _ _ gE.scopeCoins gE1.scopeCoins _).1,
        (extractMerklePathCoins_sim e stmt.issuerEpoch 0 _ _ gE.merkleCoins gE1.merkleCoins _).1]
  have hTapeE1 : checkPartyPrgTape prgExpand stmt.treeDepth repIdx (vcNextParty3 e) o.viewE1 = true := by
    rw [checkPartyPrgTape.public_eq_1]
    apply decide_eq_true
    unfold extractPartyGateCoins
    dsimp only [o, simulateOpenedBlindVcRep]
    rw [(extractSponge3Coins_sim e _ _ _ gE.attrCoins gE1.attrCoins _).2,
        (extractSponge3Coins_sim e _ _ _ gE.presCoins gE1.presCoins _).2,
        (extractSponge3Coins_sim e _ _ _ gE.scopeCoins gE1.scopeCoins _).2,
        (extractMerklePathCoins_sim e stmt.issuerEpoch 0 _ _ gE.merkleCoins gE1.merkleCoins _).2]
  change verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
    stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
    stmt.disclosedAttrs repIdx e o = true
  unfold verifyOpenedBlindVcRep
  dsimp only
  have hGuardTrue :
      (decide (o.e = e) &&
       vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs &&
       decide (o.viewE.attrShares.length = stmt.schema.arity) &&
       decide (o.viewE1.attrShares.length = stmt.schema.arity) &&
       decide (o.viewE.merkleLevels.length = stmt.treeDepth) &&
       decide (o.viewE1.merkleLevels.length = stmt.treeDepth) &&
       vcCheckPartyDisclosedShares o.e o.viewE.attrShares stmt.disclosedAttrs &&
       vcCheckPartyDisclosedShares (vcNextParty3 o.e) o.viewE1.attrShares stmt.disclosedAttrs &&
       checkPartyPrgTape prgExpand stmt.treeDepth repIdx o.e o.viewE &&
       checkPartyPrgTape prgExpand stmt.treeDepth repIdx (vcNextParty3 o.e) o.viewE1) = true := by
    have hoe : o.e = e := rfl
    have ha1 : o.viewE.attrShares.length = stmt.schema.arity := hALen1
    have ha2 : o.viewE1.attrShares.length = stmt.schema.arity := hALen2
    have hm1 : o.viewE.merkleLevels.length = stmt.treeDepth := hMkLen1
    have hm2 : o.viewE1.merkleLevels.length = stmt.treeDepth := hMkLen2
    have hd1 : vcCheckPartyDisclosedShares e o.viewE.attrShares stmt.disclosedAttrs = true := hDisc1
    have hd2 : vcCheckPartyDisclosedShares (vcNextParty3 e) o.viewE1.attrShares stmt.disclosedAttrs = true := hDisc2
    rw [hoe, decide_eq_true rfl, hAsc,
        decide_eq_true ha1, decide_eq_true ha2,
        decide_eq_true hm1, decide_eq_true hm2,
        hd1, hd2, hTapeE, hTapeE1]
    rfl
  rw [hGuardTrue]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  dsimp only [o, simulateOpenedBlindVcRep]
  rw [pairCheckSponge3Perm_sim, pairCheckSponge3Perm_sim, pairCheckSponge3Perm_sim]
  dsimp only
  rw [pairCheckMerklePath_sim]
  dsimp only
  have hCompletePair : ∀ (target : Lane6) (p : Lane6 × Lane6),
      vcPairAtLane6 (completeLane6Shares3 e target p).get e = p := by
    intro target ⟨p1, p2⟩
    unfold completeLane6Shares3 vcPairAtLane6
    rw [Triple3.get_ofFn, Triple3.get_ofFn, mkParty3At_e, mkParty3At_next]
  have hCompleteSum : ∀ (target : Lane6) (p : Lane6 × Lane6),
      vcSumLane6_3 (completeLane6Shares3 e target p).get = target := by
    intro target ⟨p1, p2⟩
    unfold completeLane6Shares3
    have hGet : (Triple3.ofFn (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2))).get =
        mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) := funext (Triple3.get_ofFn _)
    rw [hGet, vcSumLane6_3_eq]
    have hScalar : ∀ (t a b : Goldilocks),
        vcSum3 (fun i => mkParty3At e a b (Goldilocks.sub (Goldilocks.sub t a) b) i) = t := by
      intro t a b
      rw [vcSum3.public_eq_1]
      rcases fin3_eq_012 e with rfl | rfl | rfl <;>
        (dsimp only [mkParty3At];
         rw [← goldOfInt_nat t, ← goldOfInt_nat a, ← goldOfInt_nat b];
         simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega)
    have hProj0 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x0) =
        (fun i => mkParty3At e p1.x0 p2.x0 (Goldilocks.sub (Goldilocks.sub target.x0 p1.x0) p2.x0) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj1 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x1) =
        (fun i => mkParty3At e p1.x1 p2.x1 (Goldilocks.sub (Goldilocks.sub target.x1 p1.x1) p2.x1) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj2 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x2) =
        (fun i => mkParty3At e p1.x2 p2.x2 (Goldilocks.sub (Goldilocks.sub target.x2 p1.x2) p2.x2) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj3 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x3) =
        (fun i => mkParty3At e p1.x3 p2.x3 (Goldilocks.sub (Goldilocks.sub target.x3 p1.x3) p2.x3) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj4 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x4) =
        (fun i => mkParty3At e p1.x4 p2.x4 (Goldilocks.sub (Goldilocks.sub target.x4 p1.x4) p2.x4) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    have hProj5 : (fun i => (mkParty3At e p1 p2 (lane6Sub (lane6Sub target p1) p2) i).x5) =
        (fun i => mkParty3At e p1.x5 p2.x5 (Goldilocks.sub (Goldilocks.sub target.x5 p1.x5) p2.x5) i) := by
      funext i; rcases fin3_eq_012 e with rfl | rfl | rfl <;> rcases fin3_eq_012 i with rfl | rfl | rfl <;> rfl
    rw [hProj0, hProj1, hProj2, hProj3, hProj4, hProj5,
        hScalar, hScalar, hScalar, hScalar, hScalar, hScalar]
  have hBzOk : ∀ pairs : List (Goldilocks × Goldilocks),
      checkBoolZeroOutputs e pairs (completeZeroShares3 e pairs) = true := by
    intro pairs
    rw [checkBoolZeroOutputs_spec]
    refine ⟨?_, ?_⟩
    · induction pairs with
      | nil => rfl
      | cons hd tl ih =>
        rcases hd with ⟨a, b⟩
        unfold completeZeroShares3 at ih ⊢
        dsimp only [List.map]
        rw [← ih]
        congr 1
        unfold vcPairAt
        rw [Triple3.get_ofFn, Triple3.get_ofFn, mkParty3At_e, mkParty3At_next]
    · intro t ht
      obtain ⟨⟨a, b⟩, _, rfl⟩ := List.mem_map.mp ht
      have hGet : (Triple3.ofFn (mkParty3At e a b (Goldilocks.sub (Goldilocks.sub Goldilocks.zero a) b))).get =
          mkParty3At e a b (Goldilocks.sub (Goldilocks.sub Goldilocks.zero a) b) := funext (Triple3.get_ofFn _)
      rw [hGet]
      rw [vcSum3.public_eq_1]
      rcases fin3_eq_012 e with rfl | rfl | rfl <;>
        (dsimp only [mkParty3At];
         rw [← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat a, ← goldOfInt_nat b];
         simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega)
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨decide_eq_true (hCompletePair _ _), decide_eq_true (hCompleteSum _ _)⟩,
            decide_eq_true (hCompletePair _ _)⟩, decide_eq_true (hCompleteSum _ _)⟩,
          decide_eq_true (hCompletePair _ _)⟩, decide_eq_true (hCompleteSum _ _)⟩, hBzOk _⟩

private def sePiCongrRight {ι : Type} {α β : ι → Type}
    (es : ∀ i, SimpleEquiv (α i) (β i)) :
    SimpleEquiv (∀ i, α i) (∀ i, β i) where
  toFun f i := (es i).toFun (f i)
  invFun g i := (es i).invFun (g i)
  left_inv f := funext fun i => (es i).left_inv (f i)
  right_inv g := funext fun i => (es i).right_inv (g i)

/-- Multi-repetition 2-witness indistinguishability bijection (`zkMultiRepViewEquiv`, `0 Classical.choice`):
    for ANY two valid secret witnesses `wit₁, wit₂` matching the same public statement `stmt` and any
    challenge vector `chals : Fin R → Fin 3`, maps `wit₁`'s randomness space bijectively onto `wit₂`'s
    randomness space so that all `R` full `OpenedBlindVcRep` views are **structurally identical**! -/
def zkMultiRepViewEquiv
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (R : Nat) (stmt : BlindVcPublicStatement)
    (wit₁ wit₂ : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (chals : Fin R → Fin 3) :
    SimpleEquiv (Fin R → RepRandomness stmt.schema.arity stmt.treeDepth)
                (Fin R → RepRandomness stmt.schema.arity stmt.treeDepth) :=
  sePiCongrRight fun r =>
    seTrans
      (zkOpenedRepFullEquiv H prgExpand stmt wit₁ r.val (chals r))
      (seSymm (zkOpenedRepFullEquiv H prgExpand stmt wit₂ r.val (chals r)))

theorem zkMultiRepViewEquiv_indistinguishable
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (R : Nat) (stmt : BlindVcPublicStatement)
    (wit₁ wit₂ : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid₁ : BlindVcWitnessValid stmt wit₁)
    (hValid₂ : BlindVcWitnessValid stmt wit₂)
    (chals : Fin R → Fin 3)
    (rands₁ : Fin R → RepRandomness stmt.schema.arity stmt.treeDepth) :
    let rands₂ := (zkMultiRepViewEquiv H prgExpand R stmt wit₁ wit₂ chals).toFun rands₁
    ∀ r : Fin R,
      honestHybrid1Rep H prgExpand stmt wit₁ r.val (chals r) (rands₁ r) =
        simulateOpenedBlindVcRep prgExpand stmt r.val (chals r)
          ((zkOpenedRepFullEquiv H prgExpand stmt wit₁ r.val (chals r)).toFun (rands₁ r)) ∧
      honestHybrid1Rep H prgExpand stmt wit₁ r.val (chals r) (rands₁ r) =
        honestHybrid1Rep H prgExpand stmt wit₂ r.val (chals r) (rands₂ r) := by
  intro rands₂ r
  have h1 := zkOpenedRepFullEquiv_simulates H prgExpand stmt wit₁ hValid₁ r.val (chals r) (rands₁ r)
  have h2 := zkOpenedRepFullEquiv_simulates H prgExpand stmt wit₂ hValid₂ r.val (chals r) (rands₂ r)
  refine ⟨h1, ?_⟩
  rw [h1, h2]
  dsimp only [rands₂, zkMultiRepViewEquiv, sePiCongrRight, seTrans, seSymm]
  rw [(zkOpenedRepFullEquiv H prgExpand stmt wit₂ r.val (chals r)).right_inv]

def vecOfListPad : (n : Nat) → List UInt8 → Vec UInt8 n
  | 0, _ => .nil
  | n + 1, [] => .cons 0 (vecOfListPad n [])
  | n + 1, b :: bs => .cons b (vecOfListPad n bs)

private theorem vecOfListPad_toList :
    ∀ {n : Nat} {bs : List UInt8},
      bs.length = n → (vecOfListPad n bs).toList = bs
  | 0, [], _ => rfl
  | n + 1, b :: bs, hLen => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [vecOfListPad, Vec.toList]
    rw [vecOfListPad_toList hLen]

private theorem buildHonestBlindVcTriple_views_and_outs
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (seeds₁ seeds₂ salts₁ salts₂ : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth)
    (gateCoins3 : Fin 3 → PartyGateCoins stmt.treeDepth)
    (e : Fin 3)
    (hsE : seeds₁ e = seeds₂ e)
    (hsE1 : seeds₁ (vcNextParty3 e) = seeds₂ (vcNextParty3 e))
    (htE : salts₁ e = salts₂ e)
    (htE1 : salts₁ (vcNextParty3 e) = salts₂ (vcNextParty3 e)) :
    let tr₁ := buildHonestBlindVcTriple stmt wit seeds₁ salts₁ attrCoins hbCoins pbCoins mkCoins gateCoins3
    let tr₂ := buildHonestBlindVcTriple stmt wit seeds₂ salts₂ attrCoins hbCoins pbCoins mkCoins gateCoins3
    tr₁.views e = tr₂.views e ∧
    tr₁.views (vcNextParty3 e) = tr₂.views (vcNextParty3 e) ∧
    tr₁.finalOuts = tr₂.finalOuts := by
  dsimp only [buildHonestBlindVcTriple]
  rw [hsE, hsE1, htE, htE1]
  exact ⟨rfl, rfl, rfl⟩

/-- Connect real-world PRG prover (`honestPrgTriple`, Hybrid 0) unconditionally to `honestHybrid1Rep`
    and `simulateOpenedBlindVcRep`: for EVERY 32-byte hash `H` and EVERY `(seeds, salts)` triple,
    opening `honestPrgTriple` at `e` equals `honestHybrid1Rep` (and hence `simulateOpenedBlindVcRep`
    for valid witnesses) across all fields of `OpenedBlindVcRep`! -/
theorem openBlindVcRep_honestPrgTriple_eq_hybrid1
    {H : List UInt8 → List UInt8} (hH32 : ∀ m, (H m).length = 32)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (repIdx : Nat) (e : Fin 3)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth) :
    let e1 := vcNextParty3 e
    let e2 := vcUnopenedParty3 e
    let tr := honestPrgTriple prgExpand stmt wit repIdx seeds salts attrCoins hbCoins pbCoins mkCoins
    let gE := prgExpand stmt.treeDepth repIdx e (seeds e)
    let gE1 := prgExpand stmt.treeDepth repIdx e1 (seeds e1)
    let gU := prgExpand stmt.treeDepth repIdx e2 (seeds e2)
    let tr₀ := buildHonestBlindVcTriple stmt wit
      (mkParty3At e (seeds e) (seeds e1) (Vec.replicate 32 0))
      (mkParty3At e (salts e) (salts e1) (Vec.replicate 32 0))
      attrCoins hbCoins pbCoins mkCoins (mkParty3At e gE gE1 gU)
    let rawComU := vcCommitPartyView H stmt.presNonce repIdx e2 (tr₀.views e2)
      (vcPartyFinalOutAt tr₀.finalOuts e2)
    let realComU := vcCommitPartyView H stmt.presNonce repIdx e2 (tr.views e2)
      (vcPartyFinalOutAt tr.finalOuts e2)
    openBlindVcRep H stmt.presNonce repIdx tr e =
      honestHybrid1Rep H prgExpand stmt wit repIdx e
        { seedE := seeds e
          seedE1 := seeds e1
          saltE := salts e
          saltE1 := salts e1
          attrShareCoins := attrCoins
          holderBlindCoins := hbCoins
          presBlindCoins := pbCoins
          merkleStepCoins := mkCoins
          gateCoins := gU
          unopenedCommitCoins := xorBytesWithVec rawComU (vecOfListPad 32 realComU) } := by
  intro e1 e2 tr gE gE1 gU tr₀ rawComU realComU
  have hGateEq : (fun i => prgExpand stmt.treeDepth repIdx i (seeds i)) = mkParty3At e gE gE1 gU :=
    (mkParty3At_eta e (fun i => prgExpand stmt.treeDepth repIdx i (seeds i))).symm
  have hTrEq : tr = buildHonestBlindVcTriple stmt wit seeds salts attrCoins hbCoins pbCoins mkCoins
      (mkParty3At e gE gE1 gU) := by
    dsimp only [tr, honestPrgTriple]
    rw [hGateEq]
  obtain ⟨hvE, hvE1, hFo⟩ := buildHonestBlindVcTriple_views_and_outs stmt wit
    seeds (mkParty3At e (seeds e) (seeds e1) (Vec.replicate 32 0))
    salts (mkParty3At e (salts e) (salts e1) (Vec.replicate 32 0))
    attrCoins hbCoins pbCoins mkCoins (mkParty3At e gE gE1 gU) e
    (mkParty3At_e e (seeds e) (seeds e1) _).symm
    (mkParty3At_next e (seeds e) (seeds e1) _).symm
    (mkParty3At_e e (salts e) (salts e1) _).symm
    (mkParty3At_next e (salts e) (salts e1) _).symm
  have hReal32 : realComU.length = 32 := by
    simp only [realComU, vcCommitPartyView.public_eq_1]
    exact hH32 _
  unfold openBlindVcRep honestHybrid1Rep
  dsimp only [e1, e2, gE, gE1, gU, tr₀, rawComU]
  rw [xorBytesWithVec_involutive, vecOfListPad_toList hReal32]
  dsimp only [realComU, e1, e2]
  rw [hTrEq, hvE, hvE1, hFo]

/-- Every opened repetition of `honestPrgTriple` for a valid witness passes `verifyOpenedBlindVcRep = true`
    (for arbitrary `H`, `prgExpand`, `seeds`, and `salts`). -/
theorem openBlindVcRep_honestPrgTriple_verifies
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (repIdx : Nat) (e : Fin 3)
    (seeds salts : Fin 3 → Vec UInt8 32)
    (attrCoins : Vec (Goldilocks × Goldilocks) stmt.schema.arity)
    (hbCoins pbCoins : Lane4 × Lane4)
    (mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) stmt.treeDepth) :
    verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
      stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
      stmt.disclosedAttrs repIdx e
      (openBlindVcRep H stmt.presNonce repIdx
        (honestPrgTriple prgExpand stmt wit repIdx seeds salts attrCoins hbCoins pbCoins mkCoins) e) = true := by
  let e1 := vcNextParty3 e
  let e2 := vcUnopenedParty3 e
  let gE := prgExpand stmt.treeDepth repIdx e (seeds e)
  let gE1 := prgExpand stmt.treeDepth repIdx e1 (seeds e1)
  let gU := prgExpand stmt.treeDepth repIdx e2 (seeds e2)
  let hRand0 : RepRandomness stmt.schema.arity stmt.treeDepth :=
    { seedE := seeds e
      seedE1 := seeds e1
      saltE := salts e
      saltE1 := salts e1
      attrShareCoins := attrCoins
      holderBlindCoins := hbCoins
      presBlindCoins := pbCoins
      merkleStepCoins := mkCoins
      gateCoins := gU
      unopenedCommitCoins := Vec.replicate 32 0 }
  let oReal := openBlindVcRep H stmt.presNonce repIdx
    (honestPrgTriple prgExpand stmt wit repIdx seeds salts attrCoins hbCoins pbCoins mkCoins) e
  let oHyb := honestHybrid1Rep H prgExpand stmt wit repIdx e hRand0
  have hIgnoreUc : verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
      stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
      stmt.disclosedAttrs repIdx e oReal =
      verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
        stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
        stmt.disclosedAttrs repIdx e { oReal with unopenedCommit := oHyb.unopenedCommit } := rfl
  have hOpenedEq : { oReal with unopenedCommit := oHyb.unopenedCommit } = oHyb := by
    have hGateEq : (fun i => prgExpand stmt.treeDepth repIdx i (seeds i)) = mkParty3At e gE gE1 gU :=
      (mkParty3At_eta e (fun i => prgExpand stmt.treeDepth repIdx i (seeds i))).symm
    obtain ⟨hvE, hvE1, hFo⟩ := buildHonestBlindVcTriple_views_and_outs stmt wit
      seeds (mkParty3At e (seeds e) (seeds e1) (Vec.replicate 32 0))
      salts (mkParty3At e (salts e) (salts e1) (Vec.replicate 32 0))
      attrCoins hbCoins pbCoins mkCoins (mkParty3At e gE gE1 gU) e
      (mkParty3At_e e (seeds e) (seeds e1) _).symm
      (mkParty3At_next e (seeds e) (seeds e1) _).symm
      (mkParty3At_e e (salts e) (salts e1) _).symm
      (mkParty3At_next e (salts e) (salts e1) _).symm
    dsimp only [oReal, oHyb, openBlindVcRep, honestHybrid1Rep, honestPrgTriple, hRand0, e1, e2, gE, gE1, gU]
    rw [hGateEq, hvE, hvE1, hFo]
  change verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
    stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
    stmt.disclosedAttrs repIdx e oReal = true
  rw [hIgnoreUc, hOpenedEq]
  dsimp only [oHyb]
  rw [zkOpenedRepFullEquiv_simulates H prgExpand stmt wit hValid repIdx e hRand0]
  exact simulateOpenedBlindVcRep_verifies prgExpand stmt hValid.1 repIdx e _

/-! #### 2-Phase Fiat-Shamir Prover (`proveBlindVcPresentation`), Flagship Theorem, `#tooth` & Inhabitedness -/

/-- Per-repetition prover randomness `(seeds, salts, wire share coins)` for `proveBlindVcPresentation`. -/
structure ProverRepCoins (arity treeDepth : Nat) where
  seeds : Fin 3 → Vec UInt8 32
  salts : Fin 3 → Vec UInt8 32
  attrCoins : Vec (Goldilocks × Goldilocks) arity
  hbCoins : Lane4 × Lane4
  pbCoins : Lane4 × Lane4
  mkCoins : Vec ((Goldilocks × Goldilocks) × (Lane6 × Lane6)) treeDepth

def buildProverTriplesFrom
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    Nat → Nat → List BlindVcRepTriple
  | _, 0 => []
  | repIdx, count + 1 =>
    let c := proverCoins repIdx
    honestPrgTriple prgExpand stmt wit repIdx c.seeds c.salts c.attrCoins c.hbCoins c.pbCoins c.mkCoins ::
      buildProverTriplesFrom prgExpand stmt wit proverCoins (repIdx + 1) count

def tripleRound1 (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (tr : BlindVcRepTriple) : Triple3 (List UInt8) × VcRepFinalOuts3 :=
  (Triple3.ofFn (fun i => vcCommitPartyView H presNonce repIdx i (tr.views i)
     (vcPartyFinalOutAt tripleFinal i)),
   tr.finalOuts)
where
  tripleFinal := tr.finalOuts

def allTripleRound1From (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32) :
    Nat → List BlindVcRepTriple → List (Triple3 (List UInt8) × VcRepFinalOuts3)
  | _, [] => []
  | repIdx, tr :: rest => tripleRound1 H presNonce repIdx tr ::
      allTripleRound1From H presNonce (repIdx + 1) rest

def openAllTriplesFrom (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (trDigest : List UInt8) : Nat → List BlindVcRepTriple → List OpenedBlindVcRep
  | _, [] => []
  | repIdx, tr :: rest =>
    openBlindVcRep H presNonce repIdx tr (deriveBlindVcChallengeAt H trDigest repIdx) ::
      openAllTriplesFrom H presNonce trDigest (repIdx + 1) rest

/-- Constructive 2-phase Fiat-Shamir prover (`prove_selective_disclosure_with_profile`, `blind_vc.rs:1960-2118`):
    1. Executes all `profile.repetitions` 3-party ZKBoo instances from PRG seeds and commits all 3 party views;
    2. Derives `"QSAG.FS.INIT/ABSORB/SQUEEZE.V1"` Fiat-Shamir challenges `e_r ∈ {0, 1, 2}` from the full Round-1 bundle;
    3. Opens `(view[e_r], view[(e_r + 1) % 3], com[(e_r + 2) % 3], finalOuts)`. -/
def proveBlindVcPresentation
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (stmt : BlindVcPublicStatement)
    (issuerRootTag : Vec UInt8 32)
    (verifierChallenge : List UInt8)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    BlindVcPresentation :=
  let triples := buildProverTriplesFrom prgExpand stmt wit proverCoins 0 profile.repetitions
  let allRound1 := allTripleRound1From H stmt.presNonce 0 triples
  let trDigest := deriveBlindVcTranscriptDigest H verifierChallenge profile stmt.schema stmt.treeDepth
    stmt.presNonce issuerRootTag stmt.issuerEpoch
    stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
    stmt.disclosedAttrs allRound1
  { presentationNonce := stmt.presNonce
    issuerEpoch := stmt.issuerEpoch
    schemaId := stmt.schema.schemaId
    accumulatorRoot := stmt.accumulatorRoot
    issuerRootTag := issuerRootTag
    verifierScopeLimbs := stmt.verifierScopeLimbs
    disclosedAttrs := stmt.disclosedAttrs
    presCommit := stmt.presCommit
    scopeTag := stmt.scopeTag
    openedReps := openAllTriplesFrom H stmt.presNonce trDigest 0 triples }

private theorem buildProverTriplesFrom_length
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    ∀ (repIdx count : Nat),
      (buildProverTriplesFrom prgExpand stmt wit proverCoins repIdx count).length = count
  | _, 0 => rfl
  | repIdx, count + 1 => by
    dsimp only [buildProverTriplesFrom, List.length_cons]
    rw [buildProverTriplesFrom_length prgExpand stmt wit proverCoins (repIdx + 1) count]

private theorem openAllTriplesFrom_length (H : List UInt8 → List UInt8)
    (presNonce : Vec UInt8 32) (trDigest : List UInt8) :
    ∀ (repIdx : Nat) (trs : List BlindVcRepTriple),
      (openAllTriplesFrom H presNonce trDigest repIdx trs).length = trs.length
  | _, [] => rfl
  | repIdx, _ :: rest => by
    dsimp only [openAllTriplesFrom, List.length_cons]
    rw [openAllTriplesFrom_length H presNonce trDigest (repIdx + 1) rest]

private theorem reconstructAllRepRound1_openAllTriplesFrom (H : List UInt8 → List UInt8)
    (presNonce : Vec UInt8 32) (trDigest : List UInt8) :
    ∀ (repIdx : Nat) (trs : List BlindVcRepTriple),
      reconstructAllRepRound1 H presNonce repIdx (openAllTriplesFrom H presNonce trDigest repIdx trs) =
        allTripleRound1From H presNonce repIdx trs
  | _, [] => rfl
  | repIdx, tr :: rest => by
    dsimp only [openAllTriplesFrom, reconstructAllRepRound1, allTripleRound1From,
      tripleRound1, tripleRound1.tripleFinal]
    rw [reconstructRepRound1_openBlindVcRep,
        reconstructAllRepRound1_openAllTriplesFrom H presNonce trDigest (repIdx + 1) rest]

private theorem verifyAllBlindVcReps_proverTriples
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth)
    (trDigest : List UInt8) :
    ∀ (repIdx count : Nat),
      verifyAllBlindVcReps H prgExpand trDigest stmt.schema stmt.issuerEpoch stmt.treeDepth
        stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
        stmt.disclosedAttrs repIdx
        (openAllTriplesFrom H stmt.presNonce trDigest repIdx
          (buildProverTriplesFrom prgExpand stmt wit proverCoins repIdx count)) = true
  | _, 0 => rfl
  | repIdx, count + 1 => by
    dsimp only [buildProverTriplesFrom, openAllTriplesFrom, verifyAllBlindVcReps]
    rw [openBlindVcRep_honestPrgTriple_verifies H prgExpand stmt wit hValid repIdx
          (deriveBlindVcChallengeAt H trDigest repIdx),
        verifyAllBlindVcReps_proverTriples H prgExpand stmt wit hValid proverCoins trDigest (repIdx + 1) count]
    rfl

/-- **2-Phase Fiat-Shamir Prover Completeness (`proveBlindVcPresentation_verifies`)**:
    For EVERY hash `H`, PRG `prgExpand`, soundness profile `profile`, and valid secret witness `wit`,
    `proveBlindVcPresentation` produces `profile.repetitions` opened repetitions accepted by
    `verifyBlindVcPresentation = true`! -/
theorem proveBlindVcPresentation_verifies
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (stmt : BlindVcPublicStatement)
    (issuerRootTag : Vec UInt8 32)
    (verifierChallenge : List UInt8)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    let pres := proveBlindVcPresentation H prgExpand profile stmt issuerRootTag verifierChallenge wit proverCoins
    pres.openedReps.length = profile.repetitions ∧
    verifyBlindVcPresentation H prgExpand profile stmt.schema stmt.treeDepth verifierChallenge pres = true := by
  intro pres
  have hLen : pres.openedReps.length = profile.repetitions := by
    dsimp only [pres, proveBlindVcPresentation]
    rw [openAllTriplesFrom_length, buildProverTriplesFrom_length]
  refine ⟨hLen, ?_⟩
  unfold verifyBlindVcPresentation
  have hTopGuard :
      (decide (pres.schemaId = stmt.schema.schemaId) &&
       vcCheckDisclosedStrictAsc stmt.schema.arity pres.disclosedAttrs &&
       decide (pres.openedReps.length = profile.repetitions)) = true := by
    have hSid : pres.schemaId = stmt.schema.schemaId := rfl
    have hDisc : pres.disclosedAttrs = stmt.disclosedAttrs := rfl
    rw [hSid, decide_eq_true rfl, hDisc, hValid.1, decide_eq_true hLen]
    rfl
  rw [hTopGuard]
  dsimp only [Bool.not_true, ↓reduceIte, pres, proveBlindVcPresentation]
  rw [reconstructAllRepRound1_openAllTriplesFrom]
  exact verifyAllBlindVcReps_proverTriples H prgExpand stmt wit hValid proverCoins _ 0 profile.repetitions

/-- Verifier-enforced structural invariants extracted directly from `verifyBlindVcPresentation = true`
    (strict ascending `Nodup` and `profile.repetitions` are checked inside the verifier). -/
theorem verifyBlindVcPresentation_enforces_guards
    {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {profile : ZkSoundnessProfile}
    {expectedSchema : VcSchema} {treeDepth : Nat}
    {verifierChallenge : List UInt8}
    {pres : BlindVcPresentation}
    (hVer : verifyBlindVcPresentation H prgExpand profile expectedSchema treeDepth verifierChallenge pres = true) :
    pres.schemaId = expectedSchema.schemaId ∧
    pres.openedReps.length = profile.repetitions ∧
    (∀ p ∈ pres.disclosedAttrs, p.1 < expectedSchema.arity) ∧
    (pres.disclosedAttrs.map Prod.fst).Nodup := by
  unfold verifyBlindVcPresentation at hVer
  cases hG :
      (decide (pres.schemaId = expectedSchema.schemaId) &&
       vcCheckDisclosedStrictAsc expectedSchema.arity pres.disclosedAttrs &&
       decide (pres.openedReps.length = profile.repetitions)) with
  | false => rw [hG] at hVer; cases hVer
  | true =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
    obtain ⟨hBounds, hNodup⟩ := vcCheckDisclosedStrictAsc_bounds_and_nodup hG.1.2
    exact ⟨hG.1.1, hG.2, hBounds, hNodup⟩

set_option exponentiation.threshold 1024 in
/-- Verifier checks, prover completeness, commitment-bound special soundness,
repetition parameter arithmetic, and hybrid-1 fixed-challenge simulation.
The hiding component uses independent hidden tapes and an independently masked
unopened commitment. This theorem does not prove the real-to-hybrid PRG and
commitment-hiding hops, or adaptive ROM/QROM security. -/
theorem blind_vc_zkboo_selective_disclosure_sound_and_hiding
    {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D) :
    -- (1) Verifier-enforced schema, repetition count, `< arity` bounds, and `Nodup`
    (∀ (profile : ZkSoundnessProfile) (expectedSchema : VcSchema) (treeDepth : Nat)
       (verifierChallenge : List UInt8) (pres : BlindVcPresentation),
      verifyBlindVcPresentation H prgExpand profile expectedSchema treeDepth verifierChallenge pres = true →
      pres.schemaId = expectedSchema.schemaId ∧
      pres.openedReps.length = profile.repetitions ∧
      (∀ p ∈ pres.disclosedAttrs, p.1 < expectedSchema.arity) ∧
      (pres.disclosedAttrs.map Prod.fst).Nodup) ∧
    -- (2) Constructive 2-phase Fiat-Shamir prover completeness
    (∀ (profile : ZkSoundnessProfile) (stmt : BlindVcPublicStatement)
       (issuerRootTag : Vec UInt8 32) (verifierChallenge : List UInt8)
       (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth),
      BlindVcWitnessValid stmt wit →
      ∀ proverCoins,
        verifyBlindVcPresentation H prgExpand profile stmt.schema stmt.treeDepth verifierChallenge
          (proveBlindVcPresentation H prgExpand profile stmt issuerRootTag verifierChallenge wit proverCoins) = true) ∧
    -- (3) Round-1 commitment-bound 3-challenge special soundness (zero external `Nodup` premise)
    (∀ (presNonce : Vec UInt8 32) (schema : VcSchema) (issuerEpoch : UInt64) (treeDepth : Nat)
       (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
       (disclosed : List (Nat × Goldilocks)) (repIdx : Nat),
      ∀ (o0 o1 o2 : OpenedBlindVcRep),
        reconstructRepRound1 H presNonce repIdx o0 = reconstructRepRound1 H presNonce repIdx o1 →
        reconstructRepRound1 H presNonce repIdx o1 = reconstructRepRound1 H presNonce repIdx o2 →
        verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
          accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 0 o0 = true →
        verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
          accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 1 o1 = true →
        verifyOpenedBlindVcRep prgExpand schema issuerEpoch treeDepth
          accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx 2 o2 = true →
        (∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂) ∨
        ∃ (attrs : List Goldilocks) (holderBlind presBlind : Lane4)
          (leafCommit : Lane6) (boolSteps : List (Bool × Lane6)),
          (disclosed.map Prod.fst).Nodup ∧
          attrs.length = schema.arity ∧
          (∀ p ∈ disclosed, p.1 < schema.arity ∧ attrs[p.1]? = some p.2) ∧
          computeVcPoseidon2Commit schema attrs holderBlind vcAttrCommitTag = some leafCommit ∧
          boolSteps.length = treeDepth ∧
          evalVcMerklePathBool issuerEpoch 0 leafCommit boolSteps = accRoot ∧
          computeVcPoseidon2Commit schema attrs presBlind vcPresCommitTag = some presCommit ∧
          computeVcScopeTag schema.schemaId holderBlind verifierScopeLimbs = scopeTag) ∧
    -- (4) Fixed-challenge survival count and repetition parameter arithmetic
    ((∀ bad : Fin 3, ((List.finRange 3).filter (fun e => vcUnopenedParty3 e == bad)).length = 1 ∧
       ((List.finRange 3).filter (fun e => vcUnopenedParty3 e != bad)).length = 2) ∧
     ZkSoundnessProfile.classical128.repetitions = 219 ∧
     ZkSoundnessProfile.quantum128.repetitions = 438 ∧
     ratLe (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions) (1, 2 ^ 128) ∧
     ratLe (1, 2 ^ 130) (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions) ∧
     ratLe (2 ^ ZkSoundnessProfile.quantum128.repetitions, 3 ^ ZkSoundnessProfile.quantum128.repetitions) (1, 2 ^ 256)) ∧
    -- (5) Full `OpenedBlindVcRep` simulation & multi-rep 2-witness indistinguishability
    (∀ (R : Nat) (stmt : BlindVcPublicStatement)
       (wit₁ wit₂ : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth),
      BlindVcWitnessValid stmt wit₁ →
      BlindVcWitnessValid stmt wit₂ →
      ∀ (chals : Fin R → Fin 3) (rands₁ : Fin R → RepRandomness stmt.schema.arity stmt.treeDepth) (r : Fin R),
        let rands₂ := (zkMultiRepViewEquiv H prgExpand R stmt wit₁ wit₂ chals).toFun rands₁
        honestHybrid1Rep H prgExpand stmt wit₁ r.val (chals r) (rands₁ r) =
          simulateOpenedBlindVcRep prgExpand stmt r.val (chals r)
            ((zkOpenedRepFullEquiv H prgExpand stmt wit₁ r.val (chals r)).toFun (rands₁ r)) ∧
        honestHybrid1Rep H prgExpand stmt wit₁ r.val (chals r) (rands₁ r) =
          honestHybrid1Rep H prgExpand stmt wit₂ r.val (chals r) (rands₂ r)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro profile expectedSchema treeDepth verifierChallenge pres hVer
    exact verifyBlindVcPresentation_enforces_guards hVer
  · intro profile stmt issuerRootTag verifierChallenge wit hValid proverCoins
    exact (proveBlindVcPresentation_verifies H prgExpand profile stmt issuerRootTag verifierChallenge wit hValid proverCoins).2
  · intro presNonce schema issuerEpoch treeDepth accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx
      o0 o1 o2 hR1_01 hR1_12 hV0 hV1 hV2
    exact verifyOpenedBlindVcRep_extract3_from_rewound hHLen hR1_01 hR1_12 hV0 hV1 hV2
  · refine ⟨?_, zkSoundnessProfile_rom_vs_qrom_bounds.1, zkSoundnessProfile_rom_vs_qrom_bounds.2.1,
      zkSoundnessProfile_rom_vs_qrom_bounds.2.2.2.1, zkSoundnessProfile_rom_vs_qrom_bounds.2.2.2.2.1,
      zkSoundnessProfile_rom_vs_qrom_bounds.2.2.2.2.2⟩
    intro bad
    rcases fin3_eq_012 bad with rfl | rfl | rfl <;> decide
  · intro R stmt wit₁ wit₂ hV1 hV2 chals rands₁ r
    exact zkMultiRepViewEquiv_indistinguishable H prgExpand R stmt wit₁ wit₂ hV1 hV2 chals rands₁ r

/-- **`#tooth` (`tooth_blind_vc_wrong_schema_or_challenge_rejected`)**:
    Mutation-sensitivity witness proving that:
    1. Wrong `schemaId` (`pres.schemaId ≠ expectedSchema.schemaId`) deterministically rejects;
    2. Duplicate disclosed index (`pres.disclosedAttrs = [(0, v₁), (0, v₂)]`) deterministically rejects;
    3. Profile downgrade (`pres.openedReps.length = 219` against `.quantum128` requiring `438`) deterministically rejects;
    4. Wrong repetition challenge (`o.e ≠ expectedE`) deterministically rejects `verifyOpenedBlindVcRep`. -/
theorem tooth_blind_vc_wrong_schema_or_challenge_rejected
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (expectedSchema : VcSchema) (treeDepth : Nat) (verifierChallenge : List UInt8) :
    (∀ pres : BlindVcPresentation,
      pres.schemaId ≠ expectedSchema.schemaId →
      verifyBlindVcPresentation H prgExpand .quantum128 expectedSchema treeDepth verifierChallenge pres = false) ∧
    (∀ (pres : BlindVcPresentation) (v₁ v₂ : Goldilocks),
      pres.disclosedAttrs = [(0, v₁), (0, v₂)] →
      verifyBlindVcPresentation H prgExpand .quantum128 expectedSchema treeDepth verifierChallenge pres = false) ∧
    (∀ pres : BlindVcPresentation,
      pres.openedReps.length = ZkSoundnessProfile.classical128.repetitions →
      verifyBlindVcPresentation H prgExpand .quantum128 expectedSchema treeDepth verifierChallenge pres = false) ∧
    (∀ (issuerEpoch : UInt64) (accRoot presCommit scopeTag : Lane6) (verifierScopeLimbs : Lane4)
       (disclosed : List (Nat × Goldilocks)) (repIdx : Nat) (expectedE : Fin 3) (o : OpenedBlindVcRep),
      o.e ≠ expectedE →
      verifyOpenedBlindVcRep prgExpand expectedSchema issuerEpoch treeDepth
        accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expectedE o = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pres hNe
    unfold verifyBlindVcPresentation
    rw [decide_eq_false hNe]
    rfl
  · intro pres v₁ v₂ hDisc
    unfold verifyBlindVcPresentation
    have hAscFalse : vcCheckDisclosedStrictAsc expectedSchema.arity [(0, v₁), (0, v₂)] = false := by
      unfold vcCheckDisclosedStrictAsc vcCheckDisclosedStrictAscAux
      simp
    rw [hDisc, hAscFalse]
    simp
  · intro pres hLen219
    unfold verifyBlindVcPresentation
    have hNe : pres.openedReps.length ≠ ZkSoundnessProfile.quantum128.repetitions := by
      rw [hLen219]; decide
    rw [decide_eq_false hNe]
    simp
  · intro issuerEpoch accRoot presCommit scopeTag verifierScopeLimbs disclosed repIdx expectedE o hNe
    unfold verifyOpenedBlindVcRep
    dsimp only
    rw [decide_eq_false hNe]
    rfl

/-- Concrete 32-byte SP 800-185 (`0x04`-delimited) Keccak-f[1600] XOF evaluator:
    on every non-empty domain tag `tag`, `vcKeccakSponge32 (cshake256FramedPreimage tag frames)`
    equals `cshake256FramedBytes tag frames` byte-for-byte (`keccak.rs:291-295`). -/
def vcKeccakSponge32 (pre : List UInt8) : List UInt8 :=
  squeezeXofAux 32 (absorbPadded (padForRate pre 0x04))

theorem vcKeccakSponge32_eq_cshake256FramedBytes {tag : List UInt8} (hNonEmpty : tag ≠ [])
    (frames : List (List UInt8)) :
    vcKeccakSponge32 (cshake256FramedPreimage tag frames) = cshake256FramedBytes tag frames := by
  rw [cshake256FramedBytes_eq_sponge, ite_false_of hNonEmpty]
  rfl

theorem vcKeccakSponge32_length (pre : List UInt8) : (vcKeccakSponge32 pre).length = 32 := by
  unfold vcKeccakSponge32
  exact squeezeXofAux_length 32 _

/-- **Concrete `Quantum128` (`438`-Repetition) Inhabitedness Witness (`blind_vc_presentation_inhabited`)**:
    Instantiates the full 2-phase Fiat-Shamir prover & verifier over `vcKeccakSponge32`,
    `"QSAG.VC.ZKBOO_R.V1"` `vcExpandPartyCoins`, `ZkSoundnessProfile.quantum128` (`438` repetitions),
    `vcAccumulatorDepth = 20`, and non-empty selective disclosure `[(0, 42)]`
    (with **ZERO** `fun _ _ _ => 0` constant-challenge mocks!). -/
theorem blind_vc_presentation_inhabited :
    ∃ (schema : VcSchema) (pres : BlindVcPresentation),
      schema = ⟨1, 2, by decide, by decide⟩ ∧
      pres.openedReps.length = 438 ∧
      pres.disclosedAttrs = [(0, Goldilocks.ofNat 42)] ∧
      verifyBlindVcPresentation vcKeccakSponge32 vcExpandPartyCoins .quantum128
        schema vcAccumulatorDepth [0xA5, 0x5A] pres = true := by
  let schema : VcSchema := ⟨1, 2, by decide, by decide⟩
  let attrsVec : Vec Goldilocks 2 := .cons (Goldilocks.ofNat 42) (.cons (Goldilocks.ofNat 99) .nil)
  let hb : Lane4 := ⟨Goldilocks.ofNat 7, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let pb : Lane4 := ⟨Goldilocks.ofNat 11, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let mkSteps : Vec (Bool × Lane6) vcAccumulatorDepth := Vec.replicate vcAccumulatorDepth (false, lane6Zero)
  let ac := vcCommitChunks schema attrsVec.toList hb vcAttrCommitTag
  let leaf : Lane6 := state12Rate6 (absorbRate6Sponge3 ac.1 ac.2.1 ac.2.2)
  let pc := vcCommitChunks schema attrsVec.toList pb vcPresCommitTag
  let presCom : Lane6 := state12Rate6 (absorbRate6Sponge3 pc.1 pc.2.1 pc.2.2)
  let scopeLimbs : Lane4 := ⟨Goldilocks.ofNat 3, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let stmt : BlindVcPublicStatement :=
    { schema := schema
      treeDepth := vcAccumulatorDepth
      presNonce := Vec.replicate 32 0x11
      issuerEpoch := 1
      accumulatorRoot := evalVcMerklePathBool 1 0 leaf mkSteps.toList
      presCommit := presCom
      scopeTag := computeVcScopeTag schema.schemaId hb scopeLimbs
      verifierScopeLimbs := scopeLimbs
      disclosedAttrs := [(0, Goldilocks.ofNat 42)] }
  let wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth :=
    { attrs := attrsVec
      holderBlind := hb
      presBlind := pb
      merkleSteps := mkSteps }
  have hValid : BlindVcWitnessValid stmt wit := by
    refine ⟨?_, ?_, ⟨leaf, ?_, rfl⟩, ?_, rfl⟩
    · simp [stmt, schema, vcCheckDisclosedStrictAsc, vcCheckDisclosedStrictAscAux]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hNil
      · simp only [wit, attrsVec, Vec.toList, List.getElem?_cons_zero]
      · cases hNil
    · dsimp only [stmt, wit]
      unfold computeVcPoseidon2Commit
      rw [ite_true_of (Vec.toList_length attrsVec)]
    · dsimp only [stmt, wit]
      unfold computeVcPoseidon2Commit
      rw [ite_true_of (Vec.toList_length attrsVec)]
  let zeroCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth := fun _ =>
    { seeds := fun i => Vec.replicate 32 (UInt8.ofNat (i.val + 1))
      salts := fun i => Vec.replicate 32 (UInt8.ofNat (i.val + 17))
      attrCoins := Vec.replicate 2 (Goldilocks.zero, Goldilocks.zero)
      hbCoins := (lane4Zero, lane4Zero)
      pbCoins := (lane4Zero, lane4Zero)
      mkCoins := Vec.replicate vcAccumulatorDepth ((Goldilocks.zero, Goldilocks.zero), (lane6Zero, lane6Zero)) }
  let pres := proveBlindVcPresentation vcKeccakSponge32 vcExpandPartyCoins .quantum128
    stmt (Vec.replicate 32 0x22) [0xA5, 0x5A] wit zeroCoins
  obtain ⟨hLen, hVer⟩ := proveBlindVcPresentation_verifies vcKeccakSponge32 vcExpandPartyCoins .quantum128
    stmt (Vec.replicate 32 0x22) [0xA5, 0x5A] wit hValid zeroCoins
  exact ⟨schema, pres, rfl, hLen, rfl, hVer⟩


/-! ## Relying-party verification against an authenticated issuer context -/

/-- What the relying party trusts before it sees a presentation. -/
structure BlindVcTrustedContext where
  accumulatorRoot : Lane6
  issuerRootTag : Vec UInt8 32
  issuerEpoch : UInt64
  verifierScopeLimbs : Lane4

/-- Presentation verifier for a relying party. The issuer context is supplied by the
    verifier and compared before any transcript is derived, so a prover cannot present
    membership in a tree of its own making. -/
def verifyBlindVcPresentationTrusted
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (trusted : BlindVcTrustedContext)
    (expectedSchema : VcSchema) (treeDepth : Nat)
    (verifierChallenge : List UInt8)
    (pres : BlindVcPresentation) : Bool :=
  decide (pres.accumulatorRoot = trusted.accumulatorRoot ∧
    pres.issuerRootTag = trusted.issuerRootTag ∧
    pres.issuerEpoch = trusted.issuerEpoch ∧
    pres.verifierScopeLimbs = trusted.verifierScopeLimbs) &&
  verifyBlindVcPresentation H prgExpand profile expectedSchema treeDepth verifierChallenge pres

/-- An accepted presentation carries exactly the trusted context and satisfies the relation
    verifier, so every soundness statement about `verifyBlindVcPresentation` applies to it
    with the verifier's own root, issuer tag, epoch and scope. -/
theorem verifyBlindVcPresentationTrusted_context
    {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {profile : ZkSoundnessProfile} {trusted : BlindVcTrustedContext}
    {expectedSchema : VcSchema} {treeDepth : Nat} {verifierChallenge : List UInt8}
    {pres : BlindVcPresentation}
    (h : verifyBlindVcPresentationTrusted H prgExpand profile trusted expectedSchema treeDepth
      verifierChallenge pres = true) :
    pres.accumulatorRoot = trusted.accumulatorRoot ∧
    pres.issuerRootTag = trusted.issuerRootTag ∧
    pres.issuerEpoch = trusted.issuerEpoch ∧
    pres.verifierScopeLimbs = trusted.verifierScopeLimbs ∧
    verifyBlindVcPresentation H prgExpand profile expectedSchema treeDepth
      verifierChallenge pres = true := by
  unfold verifyBlindVcPresentationTrusted at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := of_decide_eq_true h.1
  exact ⟨h1, h2, h3, h4, h.2⟩

/-- A presentation built over any other accumulator root is rejected, whatever proof it
    carries. -/
theorem tooth_verifyBlindVcPresentationTrusted_foreign_root
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile) (trusted : BlindVcTrustedContext)
    (expectedSchema : VcSchema) (treeDepth : Nat) (verifierChallenge : List UInt8)
    (pres : BlindVcPresentation)
    (hRoot : pres.accumulatorRoot ≠ trusted.accumulatorRoot) :
    verifyBlindVcPresentationTrusted H prgExpand profile trusted expectedSchema treeDepth
      verifierChallenge pres = false := by
  cases h : verifyBlindVcPresentationTrusted H prgExpand profile trusted expectedSchema
      treeDepth verifierChallenge pres with
  | false => rfl
  | true => exact False.elim (hRoot (verifyBlindVcPresentationTrusted_context h).1)

/-- The honest prover is accepted under the context of its own public statement. -/
theorem proveBlindVcPresentation_verifies_trusted
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (profile : ZkSoundnessProfile)
    (stmt : BlindVcPublicStatement)
    (issuerRootTag : Vec UInt8 32)
    (verifierChallenge : List UInt8)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth)
    (hValid : BlindVcWitnessValid stmt wit)
    (proverCoins : Nat → ProverRepCoins stmt.schema.arity stmt.treeDepth) :
    verifyBlindVcPresentationTrusted H prgExpand profile
      ⟨stmt.accumulatorRoot, issuerRootTag, stmt.issuerEpoch, stmt.verifierScopeLimbs⟩
      stmt.schema stmt.treeDepth verifierChallenge
      (proveBlindVcPresentation H prgExpand profile stmt issuerRootTag verifierChallenge wit
        proverCoins) = true := by
  obtain ⟨_, hVer⟩ := proveBlindVcPresentation_verifies H prgExpand profile stmt issuerRootTag
    verifierChallenge wit hValid proverCoins
  unfold verifyBlindVcPresentationTrusted
  rw [hVer, Bool.and_true]
  exact decide_eq_true ⟨rfl, rfl, rfl, rfl⟩

theorem blindVcWitnessValid_iff (stmt : BlindVcPublicStatement)
    (wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth) :
    BlindVcWitnessValid stmt wit ↔
      (vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true ∧
      (∀ p ∈ stmt.disclosedAttrs, wit.attrs.toList[p.1]? = some p.2) ∧
      (∃ leaf : Lane6,
        computeVcPoseidon2Commit stmt.schema wit.attrs.toList wit.holderBlind vcAttrCommitTag =
          some leaf ∧
        evalVcMerklePathBool stmt.issuerEpoch 0 leaf wit.merkleSteps.toList =
          stmt.accumulatorRoot) ∧
      computeVcPoseidon2Commit stmt.schema wit.attrs.toList wit.presBlind vcPresCommitTag =
        some stmt.presCommit ∧
      computeVcScopeTag stmt.schema.schemaId wit.holderBlind stmt.verifierScopeLimbs =
        stmt.scopeTag) := Iff.rfl

#tooth_pair verifyBlindVcPresentationTrusted_context vs tooth_verifyBlindVcPresentationTrusted_foreign_root

#verify_constructive blind_vc_zkboo_selective_disclosure_sound_and_hiding


end Qsag
end
