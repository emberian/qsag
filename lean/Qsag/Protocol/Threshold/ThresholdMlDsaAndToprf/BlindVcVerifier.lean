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

