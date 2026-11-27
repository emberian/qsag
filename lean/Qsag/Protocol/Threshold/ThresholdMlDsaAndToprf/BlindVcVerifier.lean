module

public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.BlindVcCircuit
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.DkgAndSigning
public import Qsag.Math.GoldilocksEncoding
import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

/-- Domain tag `"QSAG.VC.ZKBOO_R.V1"` (`blind_vc.rs:259`, 18 bytes) for party PRG tape expansion. -/
def vcZkBooPrgTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x56, 0x43, 0x2E, 0x5A,
   0x4B, 0x42, 0x4F, 0x4F, 0x5F, 0x52, 0x2E, 0x56, 0x31]

/-- Unbounded counters in the Lean credential tape domain. -/
def vcPrgContext204 (seed : Vec UInt8 32) (rep : Nat) (party : Fin 3) (word : Nat) :
    List (List UInt8) :=
  [seed.toList, leb128 rep, [UInt8.ofNat party.val], leb128 word]

theorem vcPrgContext204_indices {seed : Vec UInt8 32} {party : Fin 3}
    {rep rep' word word' : Nat}
    (h : vcPrgContext204 seed rep party word = vcPrgContext204 seed rep' party word') :
    rep = rep' ∧ word = word' := by
  simp only [vcPrgContext204, List.cons.injEq] at h
  exact ⟨contextIndex204_injective h.2.1, contextIndex204_injective h.2.2.2.1⟩

def vcChallengeContext204 (digest : List UInt8) (rep : Nat) : List (List UInt8) :=
  [digest, leb128 rep]

theorem vcChallengeContext204_index {digest : List UInt8} {a b : Nat}
    (h : vcChallengeContext204 digest a = vcChallengeContext204 digest b) : a = b := by
  simp only [vcChallengeContext204, List.cons.injEq] at h
  exact contextIndex204_injective h.2.1

/-- Counter-mode Goldilocks PRG word stream under `"QSAG.VC.ZKBOO_R.V1"` (`blind_vc.rs:336-350`). -/
def vcPrgStreamAt (repIdx : Nat) (partyIdx : Fin 3) (tapeSeed : Vec UInt8 32) (wordIdx : Nat) : Goldilocks :=
  let blk := cshake256FramedBytes vcZkBooPrgTag
    (vcPrgContext204 tapeSeed repIdx partyIdx wordIdx)
  Goldilocks.ofNat (decodeNatLeBytes (blk.take 8))

private def sampleSboxCoins (st : Nat → Goldilocks) (pos : Nat) : SboxCoins × Nat :=
  ((st pos, st (pos + 1), st (pos + 2), st (pos + 3)), pos + 4)

private def sampleExtRoundCoins (st : Nat → Goldilocks) (pos : Nat) : ExtRoundCoins × Nat :=
  let (s0, p0) := sampleSboxCoins st pos
  let (s1, p1) := sampleSboxCoins st p0
  let (s2, p2) := sampleSboxCoins st p1
  let (s3, p3) := sampleSboxCoins st p2
  let (s4, p4) := sampleSboxCoins st p3
  let (s5, p5) := sampleSboxCoins st p4
  let (s6, p6) := sampleSboxCoins st p5
  let (s7, p7) := sampleSboxCoins st p6
  let (s8, p8) := sampleSboxCoins st p7
  let (s9, p9) := sampleSboxCoins st p8
  let (s10, p10) := sampleSboxCoins st p9
  let (s11, p11) := sampleSboxCoins st p10
  (⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩, p11)

private def sampleVecFrom {α : Type} (samp : (Nat → Goldilocks) → Nat → α × Nat)
    (st : Nat → Goldilocks) : (n : Nat) → Nat → Vec α n × Nat
  | 0, pos => (.nil, pos)
  | n + 1, pos =>
    let (h, p1) := samp st pos
    let (t, p2) := sampleVecFrom samp st n p1
    (.cons h t, p2)

private def samplePerm12Coins (st : Nat → Goldilocks) (pos : Nat) : Perm12Coins × Nat :=
  let (c1, p1) := sampleVecFrom sampleExtRoundCoins st poseidon2InitialExtConsts.length pos
  let (c2, p2) := sampleVecFrom sampleSboxCoins st poseidon2InternalConsts.length p1
  let (c3, p3) := sampleVecFrom sampleExtRoundCoins st poseidon2TerminalExtConsts.length p2
  (⟨c1, c2, c3⟩, p3)

private def sampleSponge3Coins (st : Nat → Goldilocks) (pos : Nat) : Sponge3Coins × Nat :=
  let (q1, p1) := samplePerm12Coins st pos
  let (q2, p2) := samplePerm12Coins st p1
  let (q3, p3) := samplePerm12Coins st p2
  (⟨q1, q2, q3⟩, p3)

private def sampleMerkleLevelCoins (st : Nat → Goldilocks) (pos : Nat) : MerkleLevelCoins × Nat :=
  let b := st pos
  let g0 := st (pos + 1); let g1 := st (pos + 2); let g2 := st (pos + 3)
  let g3 := st (pos + 4); let g4 := st (pos + 5); let g5 := st (pos + 6)
  let (hc, pNext) := sampleSponge3Coins st (pos + 7)
  (⟨b, g0, g1, g2, g3, g4, g5, hc⟩, pNext)

/-- Concrete `"QSAG.VC.ZKBOO_R.V1"` party PRG tape expansion (`blind_vc.rs:336-350`). -/
def vcExpandPartyCoins (treeDepth : Nat) (repIdx : Nat) (partyIdx : Fin 3) (tapeSeed : Vec UInt8 32) :
    PartyGateCoins treeDepth :=
  let st := vcPrgStreamAt repIdx partyIdx tapeSeed
  let (ac, p1) := sampleSponge3Coins st 0
  let (pc, p2) := sampleSponge3Coins st p1
  let (sc, p3) := sampleSponge3Coins st p2
  let (mc, _) := sampleVecFrom sampleMerkleLevelCoins st treeDepth p3
  ⟨ac, pc, sc, mc⟩

/-! ### §4.4 Round-1 View Commitments, PRG Tape Replay, Strict Ascending `Nodup`, Fiat-Shamir & 3-Challenge Extraction -/

/-- Concrete 3-party tuple (`DecidableEq`-friendly carrier isomorphic to `Fin 3 → α`). -/
structure Triple3 (α : Type) where
  s0 : α
  s1 : α
  s2 : α
  deriving DecidableEq, Repr

@[expose] def Triple3.get {α : Type} (t : Triple3 α) : Fin 3 → α
  | ⟨0, _⟩ => t.s0
  | ⟨1, _⟩ => t.s1
  | ⟨2, _⟩ => t.s2

@[expose] def Triple3.ofFn {α : Type} (f : Fin 3 → α) : Triple3 α :=
  ⟨f 0, f 1, f 2⟩

theorem Triple3.get_ofFn {α : Type} (f : Fin 3 → α) (i : Fin 3) :
    (Triple3.ofFn f).get i = f i := by
  rcases i with ⟨iv, hiv⟩
  have hc : iv = 0 ∨ iv = 1 ∨ iv = 2 := by omega
  rcases hc with rfl | rfl | rfl <;> rfl

private theorem Triple3.ofFn_get {α : Type} (t : Triple3 α) :
    Triple3.ofFn t.get = t := by
  cases t; rfl

theorem Triple3.ext_get {α : Type} {a b : Triple3 α}
    (h : ∀ i : Fin 3, a.get i = b.get i) : a = b := by
  cases a; cases b
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  dsimp only [Triple3.get] at h0 h1 h2
  subst h0 h1 h2; rfl

/-- Single party's full ZKBoo repetition view (`blind_vc.rs:258-325, 1805-1905`), carrying
    explicit 32-byte PRG `tapeSeed`, 32-byte broadcast commitment `commitSalt`, secret-shared
    input wires, and all gate transcripts across `attrSponge`, `merkleLevels`, `presSponge`, and `scopeSponge`. -/
structure PartyVcRepView where
  tapeSeed : Vec UInt8 32
  commitSalt : Vec UInt8 32
  attrShares : List Goldilocks
  holderBlindShare : Lane4
  presBlindShare : Lane4
  attrSponge : PartySponge3PermView
  merkleLevels : List PartyMerkleLevelView
  presSponge : PartySponge3PermView
  scopeSponge : PartySponge3PermView
  deriving DecidableEq

/-- Extract the structured gate coin tape embedded inside `v` (`none` if round/path lengths mismatch). -/
@[expose] def extractPartyGateCoins (treeDepth : Nat) (v : PartyVcRepView) : Option (PartyGateCoins treeDepth) :=
  match extractSponge3Coins v.attrSponge,
        extractSponge3Coins v.presSponge,
        extractSponge3Coins v.scopeSponge,
        extractMerklePathCoins treeDepth v.merkleLevels with
  | some ac, some pc, some sc, some mc => some ⟨ac, pc, sc, mc⟩
  | _, _, _, _ => none

/-- Verifier PRG replay check (`blind_vc.rs:365-366, 2203-2210`): every multiplication gate's
    randomness coin `r` inside `v` must match `prgExpand treeDepth repIdx partyIdx v.tapeSeed`. -/
def checkPartyPrgTape
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (treeDepth : Nat) (repIdx : Nat) (partyIdx : Fin 3) (v : PartyVcRepView) : Bool :=
  decide (extractPartyGateCoins treeDepth v = some (prgExpand treeDepth repIdx partyIdx v.tapeSeed))

/-- Single party's final output shares (`VC_FINAL_OUTPUTS = 18 + treeDepth`, `blind_vc.rs:2384-2385`). -/
structure VcPartyFinalOut where
  rootShare : Lane6
  presShare : Lane6
  scopeShare : Lane6
  boolZeroShares : List Goldilocks
  deriving DecidableEq, Repr

/-- All 3 parties' Round-1 final output shares (`final_outs_all3`, `blind_vc.rs:2366-2382`). -/
structure VcRepFinalOuts3 where
  rootShares : Triple3 Lane6
  presShares : Triple3 Lane6
  scopeShares : Triple3 Lane6
  boolZeroShares : List (Triple3 Goldilocks)
  deriving DecidableEq, Repr

@[expose] def vcPartyFinalOutAt (fo : VcRepFinalOuts3) (i : Fin 3) : VcPartyFinalOut :=
  { rootShare := fo.rootShares.get i
    presShare := fo.presShares.get i
    scopeShare := fo.scopeShares.get i
    boolZeroShares := fo.boolZeroShares.map (fun t => t.get i) }

/-- Opened ZKBoo repetition proof (`OpenedBlindVcRep`, `blind_vc.rs:760-775, 2180-2415`):
    contains Fiat-Shamir challenge `e ∈ {0, 1, 2}`, full opened `PartyVcRepView` pair `(viewE, viewE1)`
    (with `tapeSeed` and `commitSalt`), the 3rd party's Round-1 `unopenedCommit`, and `finalOuts`. -/
structure OpenedBlindVcRep where
  e : Fin 3
  viewE : PartyVcRepView
  viewE1 : PartyVcRepView
  unopenedCommit : List UInt8
  finalOuts : VcRepFinalOuts3
  deriving DecidableEq

/-- Full 3-party pre-opening repetition bundle held by the prover in Round 1. -/
structure BlindVcRepTriple where
  views : Fin 3 → PartyVcRepView
  finalOuts : VcRepFinalOuts3

/-- Selective-disclosure presentation bundle (`BlindVcPresentation`, `blind_vc.rs:740-778`). -/
structure BlindVcPresentation where
  presentationNonce : Vec UInt8 32
  issuerEpoch : UInt64
  schemaId : UInt64
  accumulatorRoot : Lane6
  issuerRootTag : Vec UInt8 32
  verifierScopeLimbs : Lane4
  disclosedAttrs : List (Nat × Goldilocks)
  presCommit : Lane6
  scopeTag : Lane6
  openedReps : List OpenedBlindVcRep
  deriving DecidableEq

/-- Strict ascending + `< arity` disclosed attribute check (`blind_vc.rs:2131-2139`):
    enforced directly inside `verifyBlindVcPresentation` rather than assumed as an external theorem hypothesis. -/
@[expose] def vcCheckDisclosedStrictAscAux (arity prev : Nat) : List (Nat × Goldilocks) → Bool
  | [] => true
  | (idx, _) :: rest =>
    decide (prev < idx) && decide (idx < arity) && vcCheckDisclosedStrictAscAux arity idx rest

@[expose] def vcCheckDisclosedStrictAsc (arity : Nat) : List (Nat × Goldilocks) → Bool
  | [] => true
  | (idx, _) :: rest => decide (idx < arity) && vcCheckDisclosedStrictAscAux arity idx rest

private theorem vcCheckDisclosedStrictAscAux_gt :
    ∀ (arity prev : Nat) (xs : List (Nat × Goldilocks)),
      vcCheckDisclosedStrictAscAux arity prev xs = true →
      ∀ p ∈ xs, prev < p.1 ∧ p.1 < arity
  | _, _, [], _, _, hp => nomatch hp
  | arity, prev, (idx, val) :: rest, hOk, p, hp => by
    simp only [vcCheckDisclosedStrictAscAux, Bool.and_eq_true, decide_eq_true_eq] at hOk
    rcases hOk with ⟨⟨hPrev, hAr⟩, hRest⟩
    rcases List.mem_cons.mp hp with rfl | hpTail
    · exact ⟨hPrev, hAr⟩
    · obtain ⟨hGt, hLt⟩ := vcCheckDisclosedStrictAscAux_gt arity idx rest hRest p hpTail
      exact ⟨Nat.lt_trans hPrev hGt, hLt⟩

private theorem vcCheckDisclosedStrictAscAux_nodup :
    ∀ (arity prev : Nat) (xs : List (Nat × Goldilocks)),
      vcCheckDisclosedStrictAscAux arity prev xs = true →
      (xs.map Prod.fst).Nodup
  | _, _, [], _ => List.Pairwise.nil
  | arity, prev, (idx, _) :: rest, hOk => by
    simp only [vcCheckDisclosedStrictAscAux, Bool.and_eq_true, decide_eq_true_eq] at hOk
    rcases hOk with ⟨_, hRest⟩
    dsimp only [List.map]
    apply List.nodup_cons.mpr
    refine ⟨?_, vcCheckDisclosedStrictAscAux_nodup arity idx rest hRest⟩
    intro hMem
    obtain ⟨p, hpMem, hpEq⟩ := List.mem_map.mp hMem
    obtain ⟨hGt, _⟩ := vcCheckDisclosedStrictAscAux_gt arity idx rest hRest p hpMem
    omega

/-- Verifier-enforced strict ascending check implies both `< arity` bounds AND `(disclosed.map Prod.fst).Nodup`. -/
theorem vcCheckDisclosedStrictAsc_bounds_and_nodup {arity : Nat} {disclosed : List (Nat × Goldilocks)}
    (hAsc : vcCheckDisclosedStrictAsc arity disclosed = true) :
    (∀ p ∈ disclosed, p.1 < arity) ∧ (disclosed.map Prod.fst).Nodup := by
  cases disclosed with
  | nil => exact ⟨(fun _ hp => nomatch hp), List.Pairwise.nil⟩
  | cons hd tl =>
    rcases hd with ⟨idx, val⟩
    simp only [vcCheckDisclosedStrictAsc, Bool.and_eq_true, decide_eq_true_eq] at hAsc
    rcases hAsc with ⟨hAr, hAux⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hpTl
      · exact hAr
      · exact (vcCheckDisclosedStrictAscAux_gt arity idx tl hAux p hpTl).2
    · dsimp only [List.map]
      apply List.nodup_cons.mpr
      refine ⟨?_, vcCheckDisclosedStrictAscAux_nodup arity idx tl hAux⟩
      intro hMem
      obtain ⟨p, hpMem, hpEq⟩ := List.mem_map.mp hMem
      obtain ⟨hGt, _⟩ := vcCheckDisclosedStrictAscAux_gt arity idx tl hAux p hpMem
      omega

/-- **`#tooth` (`tooth_duplicate_disclosed_indices_rejected`)**:
    Bounds-only checking (`∀ p ∈ xs, p.1 < 2`) accepts duplicate contradictory disclosures
    `[(0, v₁), (0, v₂)]` and unsorted `[(1, v₁), (0, v₂)]`, whereas `vcCheckDisclosedStrictAsc`
    deterministically rejects both! -/
theorem tooth_duplicate_disclosed_indices_rejected (v₁ v₂ : Goldilocks) :
    (∀ p ∈ ([(0, v₁), (0, v₂)] : List (Nat × Goldilocks)), p.1 < 2) ∧
    vcCheckDisclosedStrictAsc 2 [(0, v₁), (0, v₂)] = false ∧
    vcCheckDisclosedStrictAsc 2 [(1, v₁), (0, v₂)] = false := by
  refine ⟨?_, rfl, rfl⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp1
  · dsimp only; decide
  · rcases List.mem_cons.mp hp1 with rfl | hp2
    · dsimp only; decide
    · cases hp2

@[expose] def vcLookupDisclosed : List (Nat × Goldilocks) → Nat → Option Goldilocks
  | [], _ => none
  | (i, v) :: rest, idx => if i = idx then some v else vcLookupDisclosed rest idx

theorem vcLookupDisclosed_eq_some_of_nodup :
    ∀ {disclosed : List (Nat × Goldilocks)} {idx : Nat} {val : Goldilocks},
      (disclosed.map Prod.fst).Nodup →
      (idx, val) ∈ disclosed →
      vcLookupDisclosed disclosed idx = some val
  | [], _, _, _, hMem => nomatch hMem
  | (i, v) :: rest, idx, val, hNodup, hMem => by
    dsimp only [List.map] at hNodup
    rcases List.nodup_cons.mp hNodup with ⟨hiNotMem, hRestNodup⟩
    rcases List.mem_cons.mp hMem with hEq | hTail
    · injection hEq with hi hv
      subst hi hv
      simp [vcLookupDisclosed]
    · have hNe : i ≠ idx := by
        intro hEqIdx
        subst hEqIdx
        exact hiNotMem (List.mem_map.mpr ⟨(i, val), hTail, rfl⟩)
      simp only [vcLookupDisclosed, ite_false_of hNe]
      exact vcLookupDisclosed_eq_some_of_nodup hRestNodup hTail

theorem vcLookupDisclosed_mem :
    ∀ {disclosed : List (Nat × Goldilocks)} {idx : Nat} {val : Goldilocks},
      vcLookupDisclosed disclosed idx = some val →
      (idx, val) ∈ disclosed
  | [], _, _, h => by cases h
  | (i, v) :: rest, idx, val, h => by
    unfold vcLookupDisclosed at h
    if hEq : i = idx then
      rw [ite_true_of hEq] at h
      injection h with hv
      subst hEq hv
      exact .head rest
    else
      rw [ite_false_of hEq] at h
      exact .tail _ (vcLookupDisclosed_mem h)

/-- Publicly pinned share value for a disclosed attribute (`party 0 => val, party 1,2 => 0`). -/
@[expose] def vcExpectedDisclosedShare (partyIdx : Fin 3) (val : Goldilocks) : Goldilocks :=
  if partyIdx = 0 then val else Goldilocks.zero

@[expose] def vcCheckPartyDisclosedShares (partyIdx : Fin 3) (attrShares : List Goldilocks) :
    List (Nat × Goldilocks) → Bool
  | [] => true
  | (idx, val) :: rest =>
    decide (attrShares[idx]? = some (vcExpectedDisclosedShare partyIdx val)) &&
    vcCheckPartyDisclosedShares partyIdx attrShares rest

theorem vcCheckPartyDisclosedShares_mem {partyIdx : Fin 3} {attrShares : List Goldilocks}
    {disclosed : List (Nat × Goldilocks)}
    (hOk : vcCheckPartyDisclosedShares partyIdx attrShares disclosed = true) :
    ∀ p ∈ disclosed, attrShares[p.1]? = some (vcExpectedDisclosedShare partyIdx p.2) := by
  induction disclosed with
  | nil => intro _ hp; nomatch hp
  | cons hd tl ih =>
    rcases hd with ⟨idx, val⟩
    simp only [vcCheckPartyDisclosedShares, Bool.and_eq_true, decide_eq_true_eq] at hOk
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hpTl
    · exact hOk.1
    · exact ih hOk.2 p hpTl

/-- Domain tag `"QSAG.VC.VIEW_COM.V1"` (`blind_vc.rs:516`, 19 bytes). -/
def vcViewCommitTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x56, 0x43, 0x2E, 0x56, 0x49,
   0x45, 0x57, 0x5F, 0x43, 0x4F, 0x4D, 0x2E, 0x56, 0x31]

/-- Domain tag `"QSAG.COMMIT.V1"` (14 bytes) for salted Round-1 party-view commitments. -/
def vcMpcCommitTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x43, 0x4F, 0x4D, 0x4D, 0x49, 0x54, 0x2E, 0x56, 0x31]

/-- Domain tag `"QSAG.BLIND_VC.SD_LIMBO.V1"` (`blind_vc.rs:3224, 3822`, 25 bytes). -/
def vcSdZkDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x42, 0x4C, 0x49, 0x4E, 0x44, 0x5F,
   0x56, 0x43, 0x2E, 0x53, 0x44, 0x5F, 0x4C, 0x49, 0x4D, 0x42, 0x4F,
   0x2E, 0x56, 0x31]

/-- Alias for `"QSAG.BLIND_VC.SD_LIMBO.V1"` (`blind_vc.rs:3224, 3822`). -/
abbrev vcSdLimboDomainTag : List UInt8 := vcSdZkDomainTag

/-- Domain tag `"QSAG.MLDSA.NONCE_BURN.V2"` (`threshold_mldsa.rs:419`, 24 bytes) for durable
    nonce-burn MAC records (superseding retired `"QSAG.MLDSA.MASK_NONCE.V1"`). -/
def mldsaNonceBurnDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x4D, 0x4C, 0x44, 0x53, 0x41, 0x2E, 0x4E,
   0x4F, 0x4E, 0x43, 0x45, 0x5F, 0x42, 0x55, 0x52, 0x4E, 0x2E, 0x56, 0x32]

/-- Length-framed `cshake256_framed_32` preimage under `"QSAG.MLDSA.NONCE_BURN.V2"`. -/
def mldsaNonceBurnPreimage (macKey lockId body : List UInt8) : List UInt8 :=
  cshake256FramedPreimage mldsaNonceBurnDomainTag [macKey, lockId, body]

/-- Profile tag `"QSAG.VC.PROFILE.Quantum128:438"` (`blind_vc.rs:1746, 2166`, 30 bytes). -/
def vcProfileQuantumTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x56, 0x43, 0x2E, 0x50, 0x52,
   0x4F, 0x46, 0x49, 0x4C, 0x45, 0x2E, 0x51, 0x75, 0x61, 0x6E,
   0x74, 0x75, 0x6D, 0x31, 0x32, 0x38, 0x3A, 0x34, 0x33, 0x38]

/-- Fiat-Shamir transcript tags `"QSAG.FS.INIT.V1"`, `"QSAG.FS.ABSORB.V1"`, `"QSAG.FS.SQUEEZE.V1"`. -/
def vcFsInitTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x46, 0x53, 0x2E, 0x49, 0x4E, 0x49, 0x54, 0x2E, 0x56, 0x31]

def vcFsAbsorbTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x46, 0x53, 0x2E, 0x41, 0x42, 0x53, 0x4F, 0x52, 0x42, 0x2E, 0x56, 0x31]

def vcFsSqueezeTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x46, 0x53, 0x2E, 0x53, 0x51, 0x55, 0x45, 0x45, 0x5A, 0x45, 0x2E, 0x56, 0x31]

/-- Right-associated `u64_le`-framed chain hash over arbitrary-length frame lists:
    every sponge invocation absorbs `≤ 3` bounded frames (`< 256 ^ 8`), avoiding any upper-bound
    hypotheses on list length (`poseidon2InitialExtConsts.length`, `treeDepth`, `repetitions`). -/
def foldFramesHash (H : List UInt8 → List UInt8) (tag : List UInt8) : List (List UInt8) → List UInt8
  | [] => H (cshake256FramedPreimage tag [])
  | x :: xs => H (cshake256FramedPreimage tag [[0x01], x, foldFramesHash H tag xs])

private theorem foldFramesHash_length_lt {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8) (tag : List UInt8) (xs : List (List UInt8)) :
    (foldFramesHash H tag xs).length < 256 ^ 8 := by
  cases xs <;> simp only [foldFramesHash] <;> exact hHLen _

/-- Constructive collision reduction (`0 Classical.choice`) for `foldFramesHash`:
    whenever `∀ m, (H m).length < 256 ^ 8` and leaf frames satisfy `< 256 ^ 8`, any `xs ≠ ys`
    colliding under `foldFramesHash H tag` exhibit an explicit `H`-collision `m₁ ≠ m₂ ∧ H m₁ = H m₂`. -/
def foldFramesHashCollision
    {H : List UInt8 → List UInt8} {tag : List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {xs ys : List (List UInt8)}
    (hxB : ∀ f ∈ xs, f.length < 256 ^ 8)
    (hyB : ∀ g ∈ ys, g.length < 256 ^ 8)
    (hNe : xs ≠ ys)
    (hEq : foldFramesHash H tag xs = foldFramesHash H tag ys) :
    Σ m₁ : List UInt8, {m₂ : List UInt8 // m₁ ≠ m₂ ∧ H m₁ = H m₂} := by
  have h1Lt : ([0x01] : List UInt8).length < 256 ^ 8 := by simp only [List.length]; decide
  match xs, ys with
  | [], [] => exact False.elim (hNe rfl)
  | [], y :: ys =>
      simp only [foldFramesHash] at hEq
      refine ⟨cshake256FramedPreimage tag [],
              cshake256FramedPreimage tag [[0x01], y, foldFramesHash H tag ys], ?_, hEq⟩
      intro hPre
      have hR : ∀ g ∈ [[0x01], y, foldFramesHash H tag ys], g.length < 256 ^ 8 := by
        intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with h0 | h1 | h2 | h3
        · rw [h0]; exact h1Lt
        · rw [h1]; exact hyB y (.head ys)
        · rw [h2]; exact foldFramesHash_length_lt hHLen tag ys
        · cases h3
      have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp)
        (by intro _ hf; cases hf) hR hPre
      cases hFr
  | x :: xs, [] =>
      simp only [foldFramesHash] at hEq
      refine ⟨cshake256FramedPreimage tag [[0x01], x, foldFramesHash H tag xs],
              cshake256FramedPreimage tag [], ?_, hEq⟩
      intro hPre
      have hL : ∀ f ∈ [[0x01], x, foldFramesHash H tag xs], f.length < 256 ^ 8 := by
        intro f hf
        simp only [List.mem_cons] at hf
        rcases hf with h0 | h1 | h2 | h3
        · rw [h0]; exact h1Lt
        · rw [h1]; exact hxB x (.head xs)
        · rw [h2]; exact foldFramesHash_length_lt hHLen tag xs
        · cases h3
      have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp)
        hL (by intro _ hg; cases hg) hPre
      cases hFr
  | x :: xs, y :: ys =>
      simp only [foldFramesHash] at hEq
      let d₁ := foldFramesHash H tag xs
      let d₂ := foldFramesHash H tag ys
      have hL : ∀ f ∈ [[0x01], x, d₁], f.length < 256 ^ 8 := by
        intro f hf
        simp only [List.mem_cons] at hf
        rcases hf with h0 | h1 | h2 | h3
        · rw [h0]; exact h1Lt
        · rw [h1]; exact hxB x (.head xs)
        · rw [h2]; exact foldFramesHash_length_lt hHLen tag xs
        · cases h3
      have hR : ∀ g ∈ [[0x01], y, d₂], g.length < 256 ^ 8 := by
        intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with h0 | h1 | h2 | h3
        · rw [h0]; exact h1Lt
        · rw [h1]; exact hyB y (.head ys)
        · rw [h2]; exact foldFramesHash_length_lt hHLen tag ys
        · cases h3
      if hSub : d₁ = d₂ then
        if hx : x = y then
          have hTailNe : xs ≠ ys := fun h => hNe (by rw [hx, h])
          exact foldFramesHashCollision hHLen (fun f hf => hxB f (.tail x hf)) (fun g hg => hyB g (.tail y hg)) hTailNe hSub
        else
          refine ⟨cshake256FramedPreimage tag [[0x01], x, d₁],
                  cshake256FramedPreimage tag [[0x01], y, d₂], ?_, hEq⟩
          intro hPre
          have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hL hR hPre
          injection hFr with _ h1
          injection h1 with hxEq _
          exact hx hxEq
      else
        refine ⟨cshake256FramedPreimage tag [[0x01], x, d₁],
                cshake256FramedPreimage tag [[0x01], y, d₂], ?_, hEq⟩
        intro hPre
        have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp) hL hR hPre
        injection hFr with _ h1
        injection h1 with _ h2
        injection h2 with hdEq _
        exact hSub hdEq
termination_by xs.length

theorem foldFramesHash_collision_of_ne
    {H : List UInt8 → List UInt8} {tag : List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {xs ys : List (List UInt8)}
    (hxB : ∀ f ∈ xs, f.length < 256 ^ 8)
    (hyB : ∀ g ∈ ys, g.length < 256 ^ 8)
    (hNe : xs ≠ ys)
    (hEq : foldFramesHash H tag xs = foldFramesHash H tag ys) :
    ∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂ := by
  obtain ⟨m₁, m₂, h⟩ := foldFramesHashCollision hHLen hxB hyB hNe hEq
  exact ⟨m₁, m₂, h⟩

/-- Prefix-free structural frame serializer combinators (`∀ f, f.length ≤ 48 < 256 ^ 8`). -/
private def serListFrames {α : Type} (serElem : α → List (List UInt8)) : List α → List (List UInt8)
  | [] => [[0x00]]
  | x :: xs => [0x01] :: (serElem x ++ serListFrames serElem xs)

private theorem serListFrames_len_lt {α : Type} {serElem : α → List (List UInt8)}
    (hElem : ∀ (a : α) (f : List UInt8), f ∈ serElem a → f.length < 256 ^ 8) :
    ∀ (xs : List α) (f : List UInt8), f ∈ serListFrames serElem xs → f.length < 256 ^ 8
  | [], f, hf => by
    rcases List.mem_cons.mp hf with rfl | hNil
    · simp only [List.length]; decide
    · cases hNil
  | x :: xs, f, hf => by
    rcases List.mem_cons.mp hf with rfl | hRest
    · simp only [List.length]; decide
    · rcases List.mem_append.mp hRest with hE | hT
      · exact hElem x f hE
      · exact serListFrames_len_lt hElem xs f hT

private theorem serListFrames_prefix_inj {α : Type} {serElem : α → List (List UInt8)}
    (hElemInj : ∀ (a₁ a₂ : α) (r₁ r₂ : List (List UInt8)),
      serElem a₁ ++ r₁ = serElem a₂ ++ r₂ → a₁ = a₂ ∧ r₁ = r₂) :
    ∀ (xs₁ xs₂ : List α) (r₁ r₂ : List (List UInt8)),
      serListFrames serElem xs₁ ++ r₁ = serListFrames serElem xs₂ ++ r₂ → xs₁ = xs₂ ∧ r₁ = r₂
  | [], [], r₁, r₂, h => by
    dsimp only [serListFrames, List.cons_append, List.nil_append] at h
    injection h with _ hr
    exact ⟨rfl, hr⟩
  | [], _ :: _, _, _, h => by
    dsimp only [serListFrames, List.cons_append, List.nil_append] at h
    injection h with hTag _; cases hTag
  | _ :: _, [], _, _, h => by
    dsimp only [serListFrames, List.cons_append, List.nil_append] at h
    injection h with hTag _; cases hTag
  | x :: xs, y :: ys, r₁, r₂, h => by
    dsimp only [serListFrames, List.cons_append] at h
    injection h with _ hBody
    rw [List.append_assoc, List.append_assoc] at hBody
    obtain ⟨hxy, hRest⟩ := hElemInj x y _ _ hBody
    obtain ⟨hxs, hr⟩ := serListFrames_prefix_inj hElemInj xs ys r₁ r₂ hRest
    subst hxy hxs
    exact ⟨rfl, hr⟩

private def serGoldFrame (x : Goldilocks) : List (List UInt8) :=
  [encodeGoldilocksVecLe [x]]

private theorem serGoldFrame_inj {x y : Goldilocks} {r₁ r₂ : List (List UInt8)}
    (h : serGoldFrame x ++ r₁ = serGoldFrame y ++ r₂) : x = y ∧ r₁ = r₂ := by
  dsimp only [serGoldFrame, List.cons_append, List.nil_append] at h
  injection h with hx hr
  have hList := encodeGoldilocksVecLe_injective hx
  injection hList with hxy _
  exact ⟨hxy, hr⟩

private theorem serGoldFrame_len (x : Goldilocks) (f : List UInt8) (hf : f ∈ serGoldFrame x) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [encodeGoldilocksVecLe_length]; simp only [List.length]; decide
  · cases hNil

def serLane4Frame (x : Lane4) : List (List UInt8) :=
  [encodeGoldilocksVecLe [x.x0, x.x1, x.x2, x.x3]]

private theorem serLane4Frame_inj {x y : Lane4} {r₁ r₂ : List (List UInt8)}
    (h : serLane4Frame x ++ r₁ = serLane4Frame y ++ r₂) : x = y ∧ r₁ = r₂ := by
  dsimp only [serLane4Frame, List.cons_append, List.nil_append] at h
  injection h with hx hr
  have hList := encodeGoldilocksVecLe_injective hx
  injection hList with h0 t1; injection t1 with h1 t2; injection t2 with h2 t3; injection t3 with h3 _
  exact ⟨Lane4.ext h0 h1 h2 h3, hr⟩

private theorem serLane4Frame_len (x : Lane4) (f : List UInt8) (hf : f ∈ serLane4Frame x) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [encodeGoldilocksVecLe_length]; simp only [List.length]; decide
  · cases hNil

def serLane6Frame (x : Lane6) : List (List UInt8) :=
  [encodeGoldilocksVecLe [x.x0, x.x1, x.x2, x.x3, x.x4, x.x5]]

private theorem serLane6Frame_inj {x y : Lane6} {r₁ r₂ : List (List UInt8)}
    (h : serLane6Frame x ++ r₁ = serLane6Frame y ++ r₂) : x = y ∧ r₁ = r₂ := by
  dsimp only [serLane6Frame, List.cons_append, List.nil_append] at h
  injection h with hx hr
  have hList := encodeGoldilocksVecLe_injective hx
  injection hList with h0 t1; injection t1 with h1 t2; injection t2 with h2 t3
  injection t3 with h3 t4; injection t4 with h4 t5; injection t5 with h5 _
  exact ⟨Lane6.ext h0 h1 h2 h3 h4 h5, hr⟩

private theorem serLane6Frame_len (x : Lane6) (f : List UInt8) (hf : f ∈ serLane6Frame x) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [encodeGoldilocksVecLe_length]; simp only [List.length]; decide
  · cases hNil

private def serMulFrame (g : PartyMulView) : List (List UInt8) :=
  [encodeGoldilocksVecLe [g.r, g.out]]

private theorem serMulFrame_inj {a b : PartyMulView} {r₁ r₂ : List (List UInt8)}
    (h : serMulFrame a ++ r₁ = serMulFrame b ++ r₂) : a = b ∧ r₁ = r₂ := by
  dsimp only [serMulFrame, List.cons_append, List.nil_append] at h
  injection h with hx hr
  have hList := encodeGoldilocksVecLe_injective hx
  injection hList with h0 t1; injection t1 with h1 _
  refine ⟨?_, hr⟩
  rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩
  dsimp only at h0 h1
  rw [h0, h1]

private theorem serMulFrame_len (a : PartyMulView) (f : List UInt8) (hf : f ∈ serMulFrame a) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [encodeGoldilocksVecLe_length]; simp only [List.length]; decide
  · cases hNil

private def serSboxFrames (s : PartySboxView) : List (List UInt8) :=
  serMulFrame s.g1 ++ serMulFrame s.g2 ++ serMulFrame s.g3 ++ serMulFrame s.g4

private theorem serSboxFrames_inj {a b : PartySboxView} {r₁ r₂ : List (List UInt8)}
    (h : serSboxFrames a ++ r₁ = serSboxFrames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serSboxFrames at h
  simp only [List.append_assoc] at h
  rcases serMulFrame_inj h with ⟨e1, h1⟩
  rcases serMulFrame_inj h1 with ⟨e2, h2⟩
  rcases serMulFrame_inj h2 with ⟨e3, h3⟩
  rcases serMulFrame_inj h3 with ⟨e4, h4⟩
  refine ⟨?_, h4⟩
  rcases a with ⟨_, _, _, _⟩; rcases b with ⟨_, _, _, _⟩
  dsimp only at e1 e2 e3 e4
  rw [e1, e2, e3, e4]

private theorem serSboxFrames_len (s : PartySboxView) (f : List UInt8) (hf : f ∈ serSboxFrames s) :
    f.length < 256 ^ 8 := by
  unfold serSboxFrames at hf
  rcases List.mem_append.mp hf with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exact serMulFrame_len _ f h1
      · exact serMulFrame_len _ f h2
    · exact serMulFrame_len _ f h3
  · exact serMulFrame_len _ f h4

private def serExtRoundFrames (rv : PartyExtRoundView) : List (List UInt8) :=
  serSboxFrames rv.s0 ++ serSboxFrames rv.s1 ++ serSboxFrames rv.s2 ++ serSboxFrames rv.s3 ++
  serSboxFrames rv.s4 ++ serSboxFrames rv.s5 ++ serSboxFrames rv.s6 ++ serSboxFrames rv.s7 ++
  serSboxFrames rv.s8 ++ serSboxFrames rv.s9 ++ serSboxFrames rv.s10 ++ serSboxFrames rv.s11

private theorem serExtRoundFrames_inj {a b : PartyExtRoundView} {r₁ r₂ : List (List UInt8)}
    (h : serExtRoundFrames a ++ r₁ = serExtRoundFrames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serExtRoundFrames at h
  simp only [List.append_assoc] at h
  rcases serSboxFrames_inj h with ⟨e0, h0⟩; rcases serSboxFrames_inj h0 with ⟨e1, h1⟩
  rcases serSboxFrames_inj h1 with ⟨e2, h2⟩; rcases serSboxFrames_inj h2 with ⟨e3, h3⟩
  rcases serSboxFrames_inj h3 with ⟨e4, h4⟩; rcases serSboxFrames_inj h4 with ⟨e5, h5⟩
  rcases serSboxFrames_inj h5 with ⟨e6, h6⟩; rcases serSboxFrames_inj h6 with ⟨e7, h7⟩
  rcases serSboxFrames_inj h7 with ⟨e8, h8⟩; rcases serSboxFrames_inj h8 with ⟨e9, h9⟩
  rcases serSboxFrames_inj h9 with ⟨e10, h10⟩; rcases serSboxFrames_inj h10 with ⟨e11, h11⟩
  refine ⟨?_, h11⟩
  rcases a with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases b with ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩
  dsimp only at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]

private theorem serExtRoundFrames_len (rv : PartyExtRoundView) (f : List UInt8)
    (hf : f ∈ serExtRoundFrames rv) : f.length < 256 ^ 8 := by
  unfold serExtRoundFrames at hf
  simp only [List.mem_append] at hf
  rcases hf with (((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11)
  · exact serSboxFrames_len _ f h0
  · exact serSboxFrames_len _ f h1
  · exact serSboxFrames_len _ f h2
  · exact serSboxFrames_len _ f h3
  · exact serSboxFrames_len _ f h4
  · exact serSboxFrames_len _ f h5
  · exact serSboxFrames_len _ f h6
  · exact serSboxFrames_len _ f h7
  · exact serSboxFrames_len _ f h8
  · exact serSboxFrames_len _ f h9
  · exact serSboxFrames_len _ f h10
  · exact serSboxFrames_len _ f h11

private def serPerm12Frames (pv : PartyPerm12View) : List (List UInt8) :=
  serListFrames serExtRoundFrames pv.initExt ++
  serListFrames serSboxFrames pv.internal ++
  serListFrames serExtRoundFrames pv.termExt

private theorem serPerm12Frames_inj {a b : PartyPerm12View} {r₁ r₂ : List (List UInt8)}
    (h : serPerm12Frames a ++ r₁ = serPerm12Frames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serPerm12Frames at h
  simp only [List.append_assoc] at h
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serExtRoundFrames_inj) a.initExt b.initExt _ _ h with ⟨e1, h1⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serSboxFrames_inj) a.internal b.internal _ _ h1 with ⟨e2, h2⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serExtRoundFrames_inj) a.termExt b.termExt _ _ h2 with ⟨e3, h3⟩
  refine ⟨?_, h3⟩
  rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩
  dsimp only at e1 e2 e3
  rw [e1, e2, e3]

private theorem serPerm12Frames_len (pv : PartyPerm12View) (f : List UInt8)
    (hf : f ∈ serPerm12Frames pv) : f.length < 256 ^ 8 := by
  unfold serPerm12Frames at hf
  simp only [List.mem_append] at hf
  rcases hf with (h1 | h2) | h3
  · exact serListFrames_len_lt serExtRoundFrames_len _ f h1
  · exact serListFrames_len_lt serSboxFrames_len _ f h2
  · exact serListFrames_len_lt serExtRoundFrames_len _ f h3

private def serSponge3Frames (sv : PartySponge3PermView) : List (List UInt8) :=
  serPerm12Frames sv.perm1 ++ serPerm12Frames sv.perm2 ++ serPerm12Frames sv.perm3

private theorem serSponge3Frames_inj {a b : PartySponge3PermView} {r₁ r₂ : List (List UInt8)}
    (h : serSponge3Frames a ++ r₁ = serSponge3Frames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serSponge3Frames at h
  simp only [List.append_assoc] at h
  rcases serPerm12Frames_inj h with ⟨e1, h1⟩
  rcases serPerm12Frames_inj h1 with ⟨e2, h2⟩
  rcases serPerm12Frames_inj h2 with ⟨e3, h3⟩
  refine ⟨?_, h3⟩
  rcases a with ⟨_, _, _⟩; rcases b with ⟨_, _, _⟩
  dsimp only at e1 e2 e3
  rw [e1, e2, e3]

private theorem serSponge3Frames_len (sv : PartySponge3PermView) (f : List UInt8)
    (hf : f ∈ serSponge3Frames sv) : f.length < 256 ^ 8 := by
  unfold serSponge3Frames at hf
  simp only [List.mem_append] at hf
  rcases hf with (h1 | h2) | h3
  · exact serPerm12Frames_len _ f h1
  · exact serPerm12Frames_len _ f h2
  · exact serPerm12Frames_len _ f h3

private def serMerkleLevelFrames (lv : PartyMerkleLevelView) : List (List UInt8) :=
  serGoldFrame lv.bitShare ++ serLane6Frame lv.sibShare ++
  serMulFrame lv.boolGate ++ serMulFrame lv.sel0 ++ serMulFrame lv.sel1 ++
  serMulFrame lv.sel2 ++ serMulFrame lv.sel3 ++ serMulFrame lv.sel4 ++
  serMulFrame lv.sel5 ++ serSponge3Frames lv.hashView

private theorem serMerkleLevelFrames_inj {a b : PartyMerkleLevelView} {r₁ r₂ : List (List UInt8)}
    (h : serMerkleLevelFrames a ++ r₁ = serMerkleLevelFrames b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold serMerkleLevelFrames at h
  simp only [List.append_assoc] at h
  rcases serGoldFrame_inj h with ⟨eb, h0⟩
  rcases serLane6Frame_inj h0 with ⟨es, h1⟩
  rcases serMulFrame_inj h1 with ⟨ebg, h2⟩
  rcases serMulFrame_inj h2 with ⟨e0, h3⟩; rcases serMulFrame_inj h3 with ⟨e1, h4⟩
  rcases serMulFrame_inj h4 with ⟨e2, h5⟩; rcases serMulFrame_inj h5 with ⟨e3, h6⟩
  rcases serMulFrame_inj h6 with ⟨e4, h7⟩; rcases serMulFrame_inj h7 with ⟨e5, h8⟩
  rcases serSponge3Frames_inj h8 with ⟨eh, h9⟩
  refine ⟨?_, h9⟩
  rcases a with ⟨_, _, _, _, _, _, _, _, _, _⟩
  rcases b with ⟨_, _, _, _, _, _, _, _, _, _⟩
  dsimp only at eb es ebg e0 e1 e2 e3 e4 e5 eh
  rw [eb, es, ebg, e0, e1, e2, e3, e4, e5, eh]

private theorem serMerkleLevelFrames_len (lv : PartyMerkleLevelView) (f : List UInt8)
    (hf : f ∈ serMerkleLevelFrames lv) : f.length < 256 ^ 8 := by
  unfold serMerkleLevelFrames at hf
  simp only [List.mem_append] at hf
  rcases hf with (((((((((hb | hs) | hbg) | h0) | h1) | h2) | h3) | h4) | h5) | hh)
  · exact serGoldFrame_len _ f hb
  · exact serLane6Frame_len _ f hs
  · exact serMulFrame_len _ f hbg
  · exact serMulFrame_len _ f h0
  · exact serMulFrame_len _ f h1
  · exact serMulFrame_len _ f h2
  · exact serMulFrame_len _ f h3
  · exact serMulFrame_len _ f h4
  · exact serMulFrame_len _ f h5
  · exact serSponge3Frames_len _ f hh

private def serVec32Frame (v : Vec UInt8 32) : List (List UInt8) := [v.toList]

private theorem serVec32Frame_inj {a b : Vec UInt8 32} {r₁ r₂ : List (List UInt8)}
    (h : serVec32Frame a ++ r₁ = serVec32Frame b ++ r₂) : a = b ∧ r₁ = r₂ := by
  dsimp only [serVec32Frame, List.cons_append, List.nil_append] at h
  injection h with hv hr
  exact ⟨Vec.toList_injective hv, hr⟩

private theorem serVec32Frame_len (a : Vec UInt8 32) (f : List UInt8) (hf : f ∈ serVec32Frame a) :
    f.length < 256 ^ 8 := by
  rcases List.mem_cons.mp hf with rfl | hNil
  · rw [Vec.toList_length]; decide
  · cases hNil

/-- Full injective frame serialization of `(v.tapeSeed, v.attrShares, v.holderBlindShare,
    v.presBlindShare, v.attrSponge, v.merkleLevels, v.presSponge, v.scopeSponge, partyOut)`
    for `"QSAG.VC.VIEW_COM.V1"` (`digest_party_view`, `blind_vc.rs:514-530, 2386-2387`). -/
def serPartyViewDigestFrames (v : PartyVcRepView) (fo : VcPartyFinalOut) : List (List UInt8) :=
  serVec32Frame v.tapeSeed ++
  serListFrames serGoldFrame v.attrShares ++
  serLane4Frame v.holderBlindShare ++
  serLane4Frame v.presBlindShare ++
  serSponge3Frames v.attrSponge ++
  serListFrames serMerkleLevelFrames v.merkleLevels ++
  serSponge3Frames v.presSponge ++
  serSponge3Frames v.scopeSponge ++
  serLane6Frame fo.rootShare ++
  serLane6Frame fo.presShare ++
  serLane6Frame fo.scopeShare ++
  serListFrames serGoldFrame fo.boolZeroShares

private theorem serPartyViewDigestFrames_len (v : PartyVcRepView) (fo : VcPartyFinalOut) :
    ∀ f ∈ serPartyViewDigestFrames v fo, f.length < 256 ^ 8 := by
  intro f hf
  unfold serPartyViewDigestFrames at hf
  simp only [List.mem_append] at hf
  rcases hf with (((((((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11)
  · exact serVec32Frame_len _ f h0
  · exact serListFrames_len_lt serGoldFrame_len _ f h1
  · exact serLane4Frame_len _ f h2
  · exact serLane4Frame_len _ f h3
  · exact serSponge3Frames_len _ f h4
  · exact serListFrames_len_lt serMerkleLevelFrames_len _ f h5
  · exact serSponge3Frames_len _ f h6
  · exact serSponge3Frames_len _ f h7
  · exact serLane6Frame_len _ f h8
  · exact serLane6Frame_len _ f h9
  · exact serLane6Frame_len _ f h10
  · exact serListFrames_len_lt serGoldFrame_len _ f h11

/-- Two party views with identical `commitSalt` and identical `serPartyViewDigestFrames` are equal. -/
private theorem serPartyViewDigestFrames_injective
    {v₁ v₂ : PartyVcRepView} {fo₁ fo₂ : VcPartyFinalOut}
    (hSalt : v₁.commitSalt = v₂.commitSalt)
    (hEq : serPartyViewDigestFrames v₁ fo₁ = serPartyViewDigestFrames v₂ fo₂) :
    v₁ = v₂ ∧ fo₁ = fo₂ := by
  have hApp : serPartyViewDigestFrames v₁ fo₁ ++ [] = serPartyViewDigestFrames v₂ fo₂ ++ [] := by
    simp [hEq]
  unfold serPartyViewDigestFrames at hApp
  simp only [List.append_assoc] at hApp
  rcases serVec32Frame_inj hApp with ⟨eSeed, h0⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serGoldFrame_inj) _ _ _ _ h0 with ⟨eAttrs, h1⟩
  rcases serLane4Frame_inj h1 with ⟨eHb, h2⟩
  rcases serLane4Frame_inj h2 with ⟨ePb, h3⟩
  rcases serSponge3Frames_inj h3 with ⟨eAs, h4⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serMerkleLevelFrames_inj) _ _ _ _ h4 with ⟨eMk, h5⟩
  rcases serSponge3Frames_inj h5 with ⟨ePs, h6⟩
  rcases serSponge3Frames_inj h6 with ⟨eSs, h7⟩
  rcases serLane6Frame_inj h7 with ⟨eFr, h8⟩
  rcases serLane6Frame_inj h8 with ⟨eFp, h9⟩
  rcases serLane6Frame_inj h9 with ⟨eFs, h10⟩
  rcases serListFrames_prefix_inj (fun _ _ _ _ => serGoldFrame_inj) _ _ _ _ h10 with ⟨eFb, _⟩
  refine ⟨?_, ?_⟩
  · rcases v₁ with ⟨_, _, _, _, _, _, _, _, _⟩
    rcases v₂ with ⟨_, _, _, _, _, _, _, _, _⟩
    dsimp only at hSalt eSeed eAttrs eHb ePb eAs eMk ePs eSs
    rw [hSalt, eSeed, eAttrs, eHb, ePb, eAs, eMk, ePs, eSs]
  · rcases fo₁ with ⟨_, _, _, _⟩
    rcases fo₂ with ⟨_, _, _, _⟩
    dsimp only at eFr eFp eFs eFb
    rw [eFr, eFp, eFs, eFb]

/-- `"QSAG.VC.VIEW_COM.V1"` party-view digest (`digest_party_view`, `blind_vc.rs:514-530`). -/
def vcViewDigest (H : List UInt8 → List UInt8) (v : PartyVcRepView) (fo : VcPartyFinalOut) : List UInt8 :=
  foldFramesHash H vcViewCommitTag (serPartyViewDigestFrames v fo)

/-- Salted `"QSAG.COMMIT.V1"` Round-1 broadcast commitment (`commit_mpc_broadcast`, `blind_vc.rs:2388-2401`). -/
def vcCommitPartyViewPreimage (presNonce : Vec UInt8 32) (repIdx : Nat) (partyIdx : Fin 3)
    (viewDigest : List UInt8) (salt : Vec UInt8 32) : List UInt8 :=
  cshake256FramedPreimage vcMpcCommitTag
    [presNonce.toList, encodeNatLeBytes 8 repIdx, [UInt8.ofNat partyIdx.val], viewDigest, salt.toList]

def vcCommitPartyView (H : List UInt8 → List UInt8) (presNonce : Vec UInt8 32)
    (repIdx : Nat) (partyIdx : Fin 3) (v : PartyVcRepView) (fo : VcPartyFinalOut) : List UInt8 :=
  H (vcCommitPartyViewPreimage presNonce repIdx partyIdx (vcViewDigest H v fo) v.commitSalt)

/-- Constructive commitment binding (`0 Classical.choice`): any `(v₁, fo₁) ≠ (v₂, fo₂)` colliding
    on `vcCommitPartyView` constructively exhibit an explicit `H`-collision under either
    `"QSAG.COMMIT.V1"` or `"QSAG.VC.VIEW_COM.V1"`. -/
def vcCommitPartyViewCollision
    {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {presNonce : Vec UInt8 32} {repIdx : Nat} {partyIdx : Fin 3}
    {v₁ v₂ : PartyVcRepView} {fo₁ fo₂ : VcPartyFinalOut}
    (hNe : (v₁, fo₁) ≠ (v₂, fo₂))
    (hComEq : vcCommitPartyView H presNonce repIdx partyIdx v₁ fo₁ =
              vcCommitPartyView H presNonce repIdx partyIdx v₂ fo₂) :
    Σ m₁ : List UInt8, {m₂ : List UInt8 // m₁ ≠ m₂ ∧ H m₁ = H m₂} := by
  let d₁ := vcViewDigest H v₁ fo₁
  let d₂ := vcViewDigest H v₂ fo₂
  let pre₁ := vcCommitPartyViewPreimage presNonce repIdx partyIdx d₁ v₁.commitSalt
  let pre₂ := vcCommitPartyViewPreimage presNonce repIdx partyIdx d₂ v₂.commitSalt
  have hPreFrames : ∀ (d : List UInt8) (s : Vec UInt8 32),
      d.length < 256 ^ 8 →
      ∀ f ∈ [presNonce.toList, encodeNatLeBytes 8 repIdx, [UInt8.ofNat partyIdx.val], d, s.toList],
        f.length < 256 ^ 8 := by
    intro d s hd f hf
    rcases List.mem_cons.mp hf with rfl | h1
    · rw [Vec.toList_length]; decide
    · rcases List.mem_cons.mp h1 with rfl | h2
      · rw [encodeNatLeBytes_length]; decide
      · rcases List.mem_cons.mp h2 with rfl | h3
        · simp only [List.length]; decide
        · rcases List.mem_cons.mp h3 with rfl | h4
          · exact hd
          · rcases List.mem_cons.mp h4 with rfl | h5
            · rw [Vec.toList_length]; decide
            · cases h5
  if hPreEq : pre₁ = pre₂ then
    have hFr := cshake256FramedPreimage_frames_injective (by simp) (by simp)
      (hPreFrames d₁ v₁.commitSalt (hHLen _))
      (hPreFrames d₂ v₂.commitSalt (hHLen _)) hPreEq
    injection hFr with _ t1; injection t1 with _ t2; injection t2 with _ t3
    injection t3 with hdEq t4; injection t4 with hSaltList _
    have hSaltEq : v₁.commitSalt = v₂.commitSalt := Vec.toList_injective hSaltList
    have hFramesNe : serPartyViewDigestFrames v₁ fo₁ ≠ serPartyViewDigestFrames v₂ fo₂ := by
      intro hSerEq
      obtain ⟨hv, hfo⟩ := serPartyViewDigestFrames_injective hSaltEq hSerEq
      exact hNe (by rw [hv, hfo])
    exact foldFramesHashCollision hHLen
      (serPartyViewDigestFrames_len v₁ fo₁)
      (serPartyViewDigestFrames_len v₂ fo₂) hFramesNe hdEq
  else
    exact ⟨pre₁, pre₂, hPreEq, hComEq⟩

theorem vcCommitPartyView_binding
    {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {presNonce : Vec UInt8 32} {repIdx : Nat} {partyIdx : Fin 3}
    {v₁ v₂ : PartyVcRepView} {fo₁ fo₂ : VcPartyFinalOut}
    (hNe : (v₁, fo₁) ≠ (v₂, fo₂))
    (hComEq : vcCommitPartyView H presNonce repIdx partyIdx v₁ fo₁ =
              vcCommitPartyView H presNonce repIdx partyIdx v₂ fo₂) :
    ∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂ := by
  obtain ⟨m₁, m₂, h⟩ := vcCommitPartyViewCollision hHLen hNe hComEq
  exact ⟨m₁, m₂, h⟩

/-- Framed preimage injectivity and domain-tag parity for `"QSAG.MLDSA.NONCE_BURN.V2"` and
    `"QSAG.BLIND_VC.SD_LIMBO.V1"`. -/
theorem mldsaNonceBurnPreimage_injective
    {k₁ k₂ l₁ l₂ b₁ b₂ : List UInt8}
    (hk₁ : k₁.length < 256 ^ 8) (hk₂ : k₂.length < 256 ^ 8)
    (hl₁ : l₁.length < 256 ^ 8) (hl₂ : l₂.length < 256 ^ 8)
    (hb₁ : b₁.length < 256 ^ 8) (hb₂ : b₂.length < 256 ^ 8)
    (hEq : mldsaNonceBurnPreimage k₁ l₁ b₁ = mldsaNonceBurnPreimage k₂ l₂ b₂) :
    k₁ = k₂ ∧ l₁ = l₂ ∧ b₁ = b₂ ∧
    mldsaNonceBurnDomainTag =
      (['Q', 'S', 'A', 'G', '.', 'M', 'L', 'D', 'S', 'A', '.',
        'N', 'O', 'N', 'C', 'E', '_', 'B', 'U', 'R', 'N', '.', 'V', '2'].map
        (fun c => UInt8.ofNat c.toNat)) ∧
    vcSdLimboDomainTag =
      (['Q', 'S', 'A', 'G', '.', 'B', 'L', 'I', 'N', 'D', '_', 'V', 'C', '.',
        'S', 'D', '_', 'L', 'I', 'M', 'B', 'O', '.', 'V', '1'].map
        (fun c => UInt8.ofNat c.toNat)) := by
  unfold mldsaNonceBurnPreimage at hEq
  have hAll1 : ∀ f ∈ [k₁, l₁, b₁], f.length < 256 ^ 8 := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | h1
    · exact hk₁
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hl₁
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact hb₁
        · cases h3
  have hAll2 : ∀ g ∈ [k₂, l₂, b₂], g.length < 256 ^ 8 := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | h1
    · exact hk₂
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact hl₂
      · rcases List.mem_cons.mp h2 with rfl | h3
        · exact hb₂
        · cases h3
  have hFrEq := cshake256FramedPreimage_frames_injective (by simp) (by simp) hAll1 hAll2 hEq
  injection hFrEq with ek t1
  injection t1 with el t2
  injection t2 with eb _
  exact ⟨ek, el, eb, by decide, by decide⟩

#export_eqns vcCommitPartyView

#verify_constructive mldsaNonceBurnPreimage_injective

#export_eqns checkPartyPrgTape

end Qsag
end
