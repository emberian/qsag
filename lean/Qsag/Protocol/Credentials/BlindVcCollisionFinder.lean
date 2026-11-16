module

public import Qsag.Protocol.Credentials.BlindVcQromSecurity

/-!
Executable collision extraction, rate-6 / capacity-6 6-limb sponge coherence,
transcript-log 3-opening assembly, and multi-epoch issuer signing-log freshness
for `BlindVC`.
0. **Seed-tree openings of the 256-party presentation (`credentialGgmCollisionFinder`,
   `credentialGgmCollisionFinder_complete`)**: two accepted openings that reconstruct different
   commitment preimages at a commonly opened party yield an explicit collision. Items 1 to 3
   below are about the ternary (3-party ZKBoo) model.
1. **Finite Opening-Table Collision Reduction (`vcRewoundCollisionFinder`,
   `blindVcCollisionReduction_mass`, `blindVc_fs_collisionFinder_mass_bound`)**:
   Extracts explicit colliding byte preimages with zero guessing loss.
2. **Rate-6 / Capacity-6 Width-12 `sponge12` 6-Limb Coherence
   (`blindVc_sponge12_rate6_cap6_six_limb_coherence`)**:
   Certifies that `computeVcPoseidon2Commit`, `computeVcScopeTag`, and
   `vcMerkleHashPair` absorb rate-6 chunks with explicit `schema.arity` and `10*`
   padding into zero-initialized 6-limb capacity state and squeeze 6-limb `Lane6`
   digests (`> 2^383`), matching `crates/qsag-cred/src/blind_vc.rs:149-268`.
3. **Query-Log 3-Opening Assembly & `0-Classical` `PSum` Extractor
   (`assembleThreeOpeningsFromLog`, `blindVcExtractCollisionOrWitness`)**:
   Selects accepting `(0, 1, 2)` challenge openings from an observed transcript log
   and constructively computes either `VcHashCollision H` or `BlindVcWitnessValid`.
   Constructing three openings by quantum rewinding remains a separate upstream
   obligation.
4. **Root attestation: fresh message or logged epoch
   (`issuerRootAttestation_fresh_or_logged`,
   `issuerRootAttestationBytes_fresh_forgery_or_logged`,
   `blindVc_multi_epoch_signing_log_fresh_forgery`)**:
   an attested field tuple either belongs to a logged epoch or its 142-byte attestation
   message is absent from `issuerSignedMessages signedLog`; on wire bytes the accepted
   attestation is then an ML-DSA-44 verification of an unsigned message. Protocol-independent;
   the last theorem combines it with the ternary extraction.
-/
public section
namespace Qsag

/-- Both preimages are computational data; the certificate is erased at runtime. -/
abbrev VcHashCollision (H : List UInt8 → List UInt8) :=
  Σ m₁ : List UInt8, {m₂ : List UInt8 // m₁ ≠ m₂ ∧ H m₁ = H m₂}

/-- Select one of the three actual overlapping pairs, then descend through its
commitment and digest fold to return distinct byte strings with the same hash. -/
def vcRewoundCollisionFinder (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (nonce : Vec UInt8 32) (idx : Nat) (o0 o1 o2 : OpenedBlindVcRep) :
    Option (VcHashCollision H) :=
  if h01 : o0.viewE1 ≠ o1.viewE ∧
      vcCommitPartyView H nonce idx 1 o0.viewE1 (vcPartyFinalOutAt o1.finalOuts 1) =
      vcCommitPartyView H nonce idx 1 o1.viewE (vcPartyFinalOutAt o1.finalOuts 1) then
    some (vcCommitPartyViewCollision hHLen
      (fun he => h01.1 (congrArg Prod.fst he)) h01.2)
  else if h12 : o1.viewE1 ≠ o2.viewE ∧
      vcCommitPartyView H nonce idx 2 o1.viewE1 (vcPartyFinalOutAt o2.finalOuts 2) =
      vcCommitPartyView H nonce idx 2 o2.viewE (vcPartyFinalOutAt o2.finalOuts 2) then
    some (vcCommitPartyViewCollision hHLen
      (fun he => h12.1 (congrArg Prod.fst he)) h12.2)
  else if h20 : o2.viewE1 ≠ o0.viewE ∧
      vcCommitPartyView H nonce idx 0 o2.viewE1 (vcPartyFinalOutAt o0.finalOuts 0) =
      vcCommitPartyView H nonce idx 0 o0.viewE (vcPartyFinalOutAt o0.finalOuts 0) then
    some (vcCommitPartyViewCollision hHLen
      (fun he => h20.1 (congrArg Prod.fst he)) h20.2)
  else none

theorem vcRewoundCollisionFinder_isSome (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (nonce : Vec UInt8 32) (idx : Nat) (o0 o1 o2 : OpenedBlindVcRep) :
    (vcRewoundCollisionFinder H hHLen nonce idx o0 o1 o2).isSome =
      decide (VcRewoundCommitConflict H nonce idx o0 o1 o2) := by
  unfold vcRewoundCollisionFinder VcRewoundCommitConflict
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Scan the exact table indices used by `blindVcTableConflict`. -/
def blindVcCollisionScan {k : Nat} (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) :
    List Nat → Option (VcHashCollision H)
  | [] => none
  | idx :: rest =>
    if hIdx : idx < k then
      let cand := (Vec.get msg.openTable ⟨idx, hIdx⟩).get
      match vcRewoundCollisionFinder H hHLen stmt.presNonce idx (cand 0) (cand 1) (cand 2) with
      | some pair => some pair
      | none => blindVcCollisionScan H hHLen stmt msg rest
    else blindVcCollisionScan H hHLen stmt msg rest

theorem blindVcCollisionScan_isSome {k : Nat} (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) (indices : List Nat) :
    (blindVcCollisionScan H hHLen stmt msg indices).isSome =
      indices.any (fun idx => if hIdx : idx < k then
        let cand := (Vec.get msg.openTable ⟨idx, hIdx⟩).get
        decide (VcRewoundCommitConflict H stmt.presNonce idx (cand 0) (cand 1) (cand 2))
        else false) := by
  induction indices with
  | nil => rfl
  | cons idx rest ih =>
    simp only [blindVcCollisionScan, List.any_cons]
    split
    · rename_i hIdx
      have h := vcRewoundCollisionFinder_isSome H hHLen stmt.presNonce idx
        ((Vec.get msg.openTable ⟨idx, hIdx⟩).get 0)
        ((Vec.get msg.openTable ⟨idx, hIdx⟩).get 1)
        ((Vec.get msg.openTable ⟨idx, hIdx⟩).get 2)
      split <;> simp_all
    · rename_i hIdx
      simpa using ih

def blindVcTableCollisionFinder {k : Nat} (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) :
    Option (VcHashCollision H) :=
  blindVcCollisionScan H hHLen stmt msg (List.range k)

theorem blindVcTableCollisionFinder_isSome {k : Nat} (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) :
    (blindVcTableCollisionFinder H hHLen stmt msg).isSome = blindVcTableConflict H stmt msg := by
  rw [blindVcTableConflict_eq]
  exact blindVcCollisionScan_isSome H hHLen stmt msg (List.range k)

/-! ### Seed-tree openings of the 256-party presentation: executable collision extraction

Two accepted openings of the same round-1 commitments open 255 parties each. If they
reconstruct different commitment preimages at a party both open, those preimages collide under
`H`; the scan below returns them. -/

/-- Commitment preimage of `party` reconstructed from opening `o`. -/
def credentialGgmOpenedPreimage (prg : CredentialGgmPrg)
    (encode : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (o : CredentialGgmOpening) (party : Fin credentialSdParties) : List UInt8 :=
  encode party (o.leafSeed prg party)

/-- `party` is opened by both openings, with different preimages of equal digest. -/
@[expose] def credentialGgmOverlapConflict (H : List UInt8 → List UInt8)
    (prg : CredentialGgmPrg)
    (encode : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (a b : CredentialGgmOpening) (party : Fin credentialSdParties) : Prop :=
  party ≠ a.hidden ∧ party ≠ b.hidden ∧
  credentialGgmOpenedPreimage prg encode a party ≠ credentialGgmOpenedPreimage prg encode b party ∧
  H (credentialGgmOpenedPreimage prg encode a party) =
    H (credentialGgmOpenedPreimage prg encode b party)

instance (H : List UInt8 → List UInt8) (prg : CredentialGgmPrg)
    (encode : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (a b : CredentialGgmOpening) (party : Fin credentialSdParties) :
    Decidable (credentialGgmOverlapConflict H prg encode a b party) :=
  inferInstanceAs (Decidable (party ≠ a.hidden ∧ party ≠ b.hidden ∧
    credentialGgmOpenedPreimage prg encode a party ≠ credentialGgmOpenedPreimage prg encode b party ∧
    H (credentialGgmOpenedPreimage prg encode a party) =
      H (credentialGgmOpenedPreimage prg encode b party)))

def credentialGgmCollisionScan (H : List UInt8 → List UInt8) (prg : CredentialGgmPrg)
    (encode : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (a b : CredentialGgmOpening) : List (Fin credentialSdParties) → Option (VcHashCollision H)
  | [] => none
  | party :: rest =>
    if h : credentialGgmOverlapConflict H prg encode a b party then
      some ⟨credentialGgmOpenedPreimage prg encode a party,
        credentialGgmOpenedPreimage prg encode b party, h.2.2⟩
    else credentialGgmCollisionScan H prg encode a b rest

theorem credentialGgmCollisionScan_isSome (H : List UInt8 → List UInt8) (prg : CredentialGgmPrg)
    (encode : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (a b : CredentialGgmOpening) (parties : List (Fin credentialSdParties)) :
    (credentialGgmCollisionScan H prg encode a b parties).isSome =
      parties.any (fun party => decide (credentialGgmOverlapConflict H prg encode a b party)) := by
  induction parties with
  | nil => rfl
  | cons party rest ih =>
    simp only [credentialGgmCollisionScan, List.any_cons]
    split <;> simp_all

/-- Two accepted openings have equal commitment digests at every commonly opened party. -/
theorem credentialGgmOpenedPreimage_same_digest
    (H : List UInt8 → List UInt8) (prg : CredentialGgmPrg)
    (encode : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (commitments : Fin credentialSdParties → List UInt8) (a b : CredentialGgmOpening)
    (ha : verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments a = true)
    (hb : verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments b = true)
    (party : Fin credentialSdParties) (hpa : party ≠ a.hidden) (hpb : party ≠ b.hidden) :
    H (credentialGgmOpenedPreimage prg encode a party) =
      H (credentialGgmOpenedPreimage prg encode b party) :=
  credentialGgm_overlap_same_digest prg H encode commitments a b party ha hb hpa hpb

def credentialGgmCollisionFinder (H : List UInt8 → List UInt8) (prg : CredentialGgmPrg)
    (encode : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (a b : CredentialGgmOpening) : Option (VcHashCollision H) :=
  credentialGgmCollisionScan H prg encode a b (List.finRange credentialSdParties)

/-- **Two accepted openings that disagree at a commonly opened party yield a collision**, found
    by the scan with no guess of the party. -/
theorem credentialGgmCollisionFinder_complete
    (H : List UInt8 → List UInt8) (prg : CredentialGgmPrg)
    (encode : Fin credentialSdParties → CredentialGgmSeed → List UInt8)
    (commitments : Fin credentialSdParties → List UInt8) (a b : CredentialGgmOpening)
    (ha : verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments a = true)
    (hb : verifyCredentialGgmOpening prg (fun p seed => H (encode p seed)) commitments b = true)
    (party : Fin credentialSdParties) (hpa : party ≠ a.hidden) (hpb : party ≠ b.hidden)
    (hne : credentialGgmOpenedPreimage prg encode a party ≠
      credentialGgmOpenedPreimage prg encode b party) :
    (credentialGgmCollisionFinder H prg encode a b).isSome = true := by
  rw [credentialGgmCollisionFinder, credentialGgmCollisionScan_isSome]
  apply List.any_eq_true.mpr
  refine ⟨party, List.mem_finRange party, decide_eq_true ?_⟩
  exact ⟨hpa, hpb, hne,
    credentialGgmOpenedPreimage_same_digest H prg encode commitments a b ha hb party hpa hpb⟩

/-- A table-producing adversary may depend on the hash and its random tape. -/
def blindVcCollisionReduction {Seed : Type} {k : Nat}
    (adversary : (List UInt8 → List UInt8) → Seed →
      BlindVcPublicStatement × BlindVcParallelMsg k)
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (seed : Seed) : Option (VcHashCollision H) :=
  let out := adversary H seed
  blindVcTableCollisionFinder H hHLen out.1 out.2

/-- Exact weighted event reduction, hence no guessing loss for either the
repetition index or one of its three conflicting view pairs. Normalizing both
sides by the same total seed weight gives the probability equality. -/
theorem blindVcCollisionReduction_mass {Seed : Type} {k : Nat}
    (adversary : (List UInt8 → List UInt8) → Seed →
      BlindVcPublicStatement × BlindVcParallelMsg k)
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (seeds : List Seed) (weight : Seed → Nat) :
    (seeds.map (fun seed => if (blindVcCollisionReduction adversary H hHLen seed).isSome
      then weight seed else 0)).sum =
    (seeds.map (fun seed => if blindVcTableConflict H (adversary H seed).1
      (adversary H seed).2 then weight seed else 0)).sum := by
  simp only [blindVcCollisionReduction, blindVcTableCollisionFinder_isSome]

/-- The original acceptance game splits into a returned collision or the
existing filtered acceptance game, now with computational output on the bad arm. -/
theorem blindVc_fs_collisionFinder_decomposition {cardX k : Nat}
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : Fin cardX → BlindVcParallelMsg k)
    (O : Fin cardX → BitVec (64 * k)) (x : Fin cardX)
    (hAccept : blindVcFsUnfilteredLiveAfter H prgExpand stmtAt msgAt O x = true) :
    (blindVcTableCollisionFinder H hHLen (stmtAt x) (msgAt x)).isSome = true ∨
    blindVcFsLiveAfter H prgExpand stmtAt msgAt O x = true := by
  rw [blindVcTableCollisionFinder_isSome]
  exact blindVc_fs_acceptance_decomposition H prgExpand stmtAt msgAt O x hAccept

/-- Weighted union bound for the actual unfiltered acceptance predicate. A
computational collision bound can now be applied to the executable bad arm;
its hash-query/runtime overhead still needs a separate resource analysis. -/
theorem blindVc_fs_collisionFinder_mass_bound {cardX k : Nat}
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : Fin cardX → BlindVcParallelMsg k)
    (O : Fin cardX → BitVec (64 * k)) (seeds : List (Fin cardX))
    (weight : Fin cardX → Nat) :
    (seeds.map (fun x => if blindVcFsUnfilteredLiveAfter H prgExpand stmtAt msgAt O x
      then weight x else 0)).sum ≤
    (seeds.map (fun x => if (blindVcTableCollisionFinder H hHLen (stmtAt x) (msgAt x)).isSome
      then weight x else 0)).sum +
    (seeds.map (fun x => if blindVcFsLiveAfter H prgExpand stmtAt msgAt O x
      then weight x else 0)).sum := by
  induction seeds with
  | nil => simp
  | cons x rest ih =>
    have hp := blindVc_fs_collisionFinder_decomposition H hHLen prgExpand stmtAt msgAt O x
    simp only [List.map_cons, List.sum_cons]
    cases ha : blindVcFsUnfilteredLiveAfter H prgExpand stmtAt msgAt O x <;>
      cases hc : (blindVcTableCollisionFinder H hHLen (stmtAt x) (msgAt x)).isSome <;>
      cases hf : blindVcFsLiveAfter H prgExpand stmtAt msgAt O x <;>
      simp_all <;> omega

/-- A consistent honest table produces no spurious collision. -/
theorem vcRewoundCollisionFinder_honest
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (nonce : Vec UInt8 32) (idx : Nat) (tr : BlindVcRepTriple) :
    (vcRewoundCollisionFinder H hHLen nonce idx
      (openBlindVcRep H nonce idx tr 0) (openBlindVcRep H nonce idx tr 1)
      (openBlindVcRep H nonce idx tr 2)).isSome = false := by
  rw [vcRewoundCollisionFinder_isSome]
  simp only [vcRewoundCommitConflict_honest_table, decide_false]

#verify_constructive
  vcRewoundCollisionFinder_isSome blindVcCollisionScan_isSome
  blindVcTableCollisionFinder_isSome blindVcCollisionReduction_mass
  blindVc_fs_collisionFinder_decomposition blindVc_fs_collisionFinder_mass_bound
  vcRewoundCollisionFinder_honest
  credentialGgmOpenedPreimage_same_digest
  credentialGgmCollisionScan_isSome credentialGgmCollisionFinder_complete


/-! ## §2. Rate-6 / Capacity-6 6-Limb Sponge Coherence, Log-Based 3-Opening Extraction & Multi-Epoch Signing-Log Freshness -/

/-- Select the first accepting opening for challenge trit `targetE ∈ Fin 3` from an
    adaptive/measured transcript query log for repetition `repIdx` and Round-1 commitment `r1`. -/
def findTritOpeningInLog
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement) (repIdx : Nat)
    (r1 : Triple3 (List UInt8) × VcRepFinalOuts3) (targetE : Fin 3) :
    List OpenedBlindVcRep → Option OpenedBlindVcRep
  | [] => none
  | o :: rest =>
    if verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 targetE o then some o
    else findTritOpeningInLog H prgExpand stmt repIdx r1 targetE rest

theorem findTritOpeningInLog_sound
    {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {stmt : BlindVcPublicStatement} {repIdx : Nat}
    {r1 : Triple3 (List UInt8) × VcRepFinalOuts3} {targetE : Fin 3} :
    ∀ {log : List OpenedBlindVcRep} {o : OpenedBlindVcRep},
      findTritOpeningInLog H prgExpand stmt repIdx r1 targetE log = some o →
      o ∈ log ∧ verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 targetE o = true
  | [], _, h => by cases h
  | hd :: rest, o, h => by
    unfold findTritOpeningInLog at h
    cases hv : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 targetE hd with
    | true =>
      rw [hv] at h; simp only [↓reduceIte, Option.some.injEq] at h
      subst h; exact ⟨.head rest, hv⟩
    | false =>
      rw [hv] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hMem, hOk⟩ := findTritOpeningInLog_sound h
      exact ⟨.tail hd hMem, hOk⟩

/-- Assemble a 3-challenge `(0, 1, 2)` opening tuple for repetition `repIdx` from a transcript log. -/
def assembleThreeOpeningsFromLog
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement) (repIdx : Nat)
    (r1 : Triple3 (List UInt8) × VcRepFinalOuts3)
    (log : List OpenedBlindVcRep) :
    Option (OpenedBlindVcRep × OpenedBlindVcRep × OpenedBlindVcRep) :=
  match findTritOpeningInLog H prgExpand stmt repIdx r1 0 log,
        findTritOpeningInLog H prgExpand stmt repIdx r1 1 log,
        findTritOpeningInLog H prgExpand stmt repIdx r1 2 log with
  | some o0, some o1, some o2 => some (o0, o1, o2)
  | _, _, _ => none

theorem assembleThreeOpeningsFromLog_sound
    {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {stmt : BlindVcPublicStatement} {repIdx : Nat}
    {r1 : Triple3 (List UInt8) × VcRepFinalOuts3} {log : List OpenedBlindVcRep}
    {o0 o1 o2 : OpenedBlindVcRep}
    (hAsm : assembleThreeOpeningsFromLog H prgExpand stmt repIdx r1 log = some (o0, o1, o2)) :
    verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 0 o0 = true ∧
    verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 1 o1 = true ∧
    verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 2 o2 = true := by
  unfold assembleThreeOpeningsFromLog at hAsm
  cases h0 : findTritOpeningInLog H prgExpand stmt repIdx r1 0 log <;>
    cases h1 : findTritOpeningInLog H prgExpand stmt repIdx r1 1 log <;>
    cases h2 : findTritOpeningInLog H prgExpand stmt repIdx r1 2 log <;>
    rw [h0, h1, h2] at hAsm <;> cases hAsm
  exact ⟨(findTritOpeningInLog_sound h0).2, (findTritOpeningInLog_sound h1).2,
         (findTritOpeningInLog_sound h2).2⟩

private theorem blindVc_witness_of_collisionFinder_none
    {H : List UInt8 → List UInt8} (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {stmt : BlindVcPublicStatement} {repIdx : Nat}
    {r1 : Triple3 (List UInt8) × VcRepFinalOuts3}
    {o0 o1 o2 : OpenedBlindVcRep}
    (h0 : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 0 o0 = true)
    (h1 : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 1 o1 = true)
    (h2 : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 2 o2 = true)
    (hNone : vcRewoundCollisionFinder H hHLen stmt.presNonce repIdx o0 o1 o2 = none) :
    ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth, BlindVcWitnessValid stmt wit := by
  have hNoConf : ¬ VcRewoundCommitConflict H stmt.presNonce repIdx o0 o1 o2 := by
    intro hc
    have hSome := vcRewoundCollisionFinder_isSome H hHLen stmt.presNonce repIdx o0 o1 o2
    rw [hNone, decide_eq_true hc] at hSome
    cases hSome
  obtain ⟨hR0, hV0⟩ := verifyCommittedBlindVcRep_eq_true_iff.mp h0
  obtain ⟨hR1, hV1⟩ := verifyCommittedBlindVcRep_eq_true_iff.mp h1
  obtain ⟨hR2, hV2⟩ := verifyCommittedBlindVcRep_eq_true_iff.mp h2
  rcases verifyOpenedBlindVcRep_extract3_finite_conflict
      (hR1_01 := hR0.trans hR1.symm) (hR1_12 := hR1.trans hR2.symm) hV0 hV1 hV2 with hConf | hExt
  · exact False.elim (hNoConf hConf)
  · obtain ⟨attrs, hb, pb, leaf, steps, _, hAr, hDisc, hLeaf, hSLen, hRoot, hPres, hScope⟩ := hExt
    exact blindVcWitnessValid_of_extraction (verifyOpenedBlindVcRep_disclosedStrictAsc hV0)
      hAr hSLen (fun p hp => (hDisc p hp).2) hLeaf hRoot hPres hScope

/-- **Constructive `0-Classical` (`PSum`) 3-Opening Extractor (`blindVcExtractCollisionOrWitness`)**:
    Given three accepting opened transcripts `(o0, o1, o2)` on challenge trits `(0, 1, 2)` for a
    shared Round-1 commitment `r1`, constructively computes EITHER an explicit byte-pair collision
    `VcHashCollision H` (`Type`-level data via `vcRewoundCollisionFinder`) OR a proof that `stmt`
    admits a valid `BlindVcSecretWitness`. -/
def blindVcExtractCollisionOrWitness
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement) (repIdx : Nat)
    (r1 : Triple3 (List UInt8) × VcRepFinalOuts3)
    (o0 o1 o2 : OpenedBlindVcRep)
    (h0 : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 0 o0 = true)
    (h1 : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 1 o1 = true)
    (h2 : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 2 o2 = true) :
    PSum (VcHashCollision H)
      (∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth, BlindVcWitnessValid stmt wit) :=
  match hFind : vcRewoundCollisionFinder H hHLen stmt.presNonce repIdx o0 o1 o2 with
  | some col => .inl col
  | none => .inr (blindVc_witness_of_collisionFinder_none hHLen h0 h1 h2 hFind)

theorem blindVcExtractCollisionOrWitness_sound
    {H : List UInt8 → List UInt8} (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {stmt : BlindVcPublicStatement} {repIdx : Nat}
    {r1 : Triple3 (List UInt8) × VcRepFinalOuts3}
    {o0 o1 o2 : OpenedBlindVcRep}
    (h0 : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 0 o0 = true)
    (h1 : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 1 o1 = true)
    (h2 : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 2 o2 = true) :
    match blindVcExtractCollisionOrWitness H hHLen prgExpand stmt repIdx r1 o0 o1 o2 h0 h1 h2 with
    | .inl col => col.2.1 ≠ col.1 ∧ H col.1 = H col.2.1
    | .inr _ => ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth,
        BlindVcWitnessValid stmt wit := by
  cases blindVcExtractCollisionOrWitness H hHLen prgExpand stmt repIdx r1 o0 o1 o2 h0 h1 h2 with
  | inl col => exact ⟨col.2.2.1.symm, col.2.2.2⟩
  | inr hWit => exact hWit

/-- On any false statement `¬ inLang stmt`, whenever a transcript query log `log` contains valid
    openings for all 3 trits `(0, 1, 2)` of repetition `repIdx`, `vcRewoundCollisionFinder` on the
    assembled triple deterministically outputs `some col` (`isSome = true`, zero guessing loss). -/
theorem assembleThreeOpeningsFromLog_extracts_collision_of_not_inLang
    {H : List UInt8 → List UInt8} (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {stmt : BlindVcPublicStatement} {repIdx : Nat}
    {r1 : Triple3 (List UInt8) × VcRepFinalOuts3} {log : List OpenedBlindVcRep}
    {o0 o1 o2 : OpenedBlindVcRep}
    (hFalse : ¬ ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth,
      BlindVcWitnessValid stmt wit)
    (hAsm : assembleThreeOpeningsFromLog H prgExpand stmt repIdx r1 log = some (o0, o1, o2)) :
    (vcRewoundCollisionFinder H hHLen stmt.presNonce repIdx o0 o1 o2).isSome = true := by
  obtain ⟨h0, h1, h2⟩ := assembleThreeOpeningsFromLog_sound hAsm
  cases hFind : vcRewoundCollisionFinder H hHLen stmt.presNonce repIdx o0 o1 o2 with
  | some _ => rfl
  | none => exact False.elim (hFalse (blindVc_witness_of_collisionFinder_none hHLen h0 h1 h2 hFind))

/-- Exact list of root-attestation byte messages signed by the issuer across a multi-epoch log. -/
def issuerSignedMessages {schema : VcSchema} {treeDepth : Nat}
    (signedLog : List (IssuerMintedEpoch schema treeDepth)) : List (List UInt8) :=
  signedLog.map (fun ep => ep.attestationFields.message)

private def findMatchingLoggedEpoch {schema : VcSchema} {treeDepth : Nat}
    (f : IssuerRootAttestationFields) :
    List (IssuerMintedEpoch schema treeDepth) → Option (IssuerMintedEpoch schema treeDepth)
  | [] => none
  | ep :: rest =>
    if ep.attestationFields = f then some ep else findMatchingLoggedEpoch f rest

private theorem findMatchingLoggedEpoch_some {schema : VcSchema} {treeDepth : Nat}
    {f : IssuerRootAttestationFields} :
    ∀ {log : List (IssuerMintedEpoch schema treeDepth)} {ep : IssuerMintedEpoch schema treeDepth},
      findMatchingLoggedEpoch f log = some ep → ep ∈ log ∧ ep.attestationFields = f
  | [], _, h => by cases h
  | hd :: rest, ep, h => by
    unfold findMatchingLoggedEpoch at h
    by_cases hc : hd.attestationFields = f
    · rw [ite_eq_left hc] at h
      cases h
      exact ⟨.head rest, hc⟩
    · rw [ite_eq_right hc] at h
      obtain ⟨hMem, hf⟩ := findMatchingLoggedEpoch_some h
      exact ⟨.tail hd hMem, hf⟩

private theorem findMatchingLoggedEpoch_none_not_mem_signedMessages
    {schema : VcSchema} {treeDepth : Nat} {f : IssuerRootAttestationFields} :
    ∀ {log : List (IssuerMintedEpoch schema treeDepth)},
      findMatchingLoggedEpoch f log = none → f.message ∉ issuerSignedMessages log
  | [], _, hMem => nomatch hMem
  | hd :: rest, hNone, hMem => by
    unfold findMatchingLoggedEpoch at hNone
    by_cases hc : hd.attestationFields = f
    · rw [ite_eq_left hc] at hNone
      cases hNone
    · rw [ite_eq_right hc] at hNone
      unfold issuerSignedMessages at hMem
      rw [List.map_cons] at hMem
      rcases List.mem_cons.mp hMem with hEqMsg | hInRest
      · exact hc (IssuerRootAttestationFields.message_injective hEqMsg.symm)
      · exact findMatchingLoggedEpoch_none_not_mem_signedMessages hNone hInRest

/-- **Root attestation: fresh message or logged epoch
(`issuerRootAttestation_fresh_or_logged`)**. For any issuer signing log, a field tuple either
is the tuple of a logged epoch, or its attestation message is none of the messages the issuer
signed. This holds for every presentation protocol placed behind the attestation. -/
theorem issuerRootAttestation_fresh_or_logged {schema : VcSchema} {treeDepth : Nat}
    (signedLog : List (IssuerMintedEpoch schema treeDepth)) (f : IssuerRootAttestationFields) :
    f.message ∉ issuerSignedMessages signedLog ∨
    ∃ ep ∈ signedLog, ep.attestationFields = f := by
  cases hMatch : findMatchingLoggedEpoch f signedLog with
  | none => exact Or.inl (findMatchingLoggedEpoch_none_not_mem_signedMessages hMatch)
  | some ep =>
    obtain ⟨hMem, hf⟩ := findMatchingLoggedEpoch_some hMatch
    exact Or.inr ⟨ep, hMem, hf⟩

/-- **Wire-level fresh-message forgery (`issuerRootAttestationBytes_fresh_forgery_or_logged`)**.
An attestation accepted by the ML-DSA-44 wire verifier for fields that belong to no logged
epoch is an accepted `(pk, message, context, signature)` whose message the issuer never signed. -/
theorem issuerRootAttestationBytes_fresh_forgery_or_logged {schema : VcSchema} {treeDepth : Nat}
    (signedLog : List (IssuerMintedEpoch schema treeDepth)) {byteBudget : Nat}
    {issuerPk : List UInt8} {f : IssuerRootAttestationFields} {sig : List UInt8}
    (hVer : verifyIssuerRootAttestationBytes byteBudget issuerPk f sig = true) :
    (mldsaVerifyBytes204 byteBudget issuerPk f.message issuerRootAttestationCtx sig = true ∧
      f.message ∉ issuerSignedMessages signedLog) ∨
    ∃ ep ∈ signedLog, ep.attestationFields = f := by
  rcases issuerRootAttestation_fresh_or_logged signedLog f with hFresh | hLogged
  · exact Or.inl ⟨hVer, hFresh⟩
  · exact Or.inr hLogged

/-- **Multi-Epoch Signing-Log Fresh-Message & Collision Reduction, ternary presentation model
    (`blindVc_multi_epoch_signing_log_fresh_forgery`)**:
    any accepted ternary presentation with 3 consistent openings `(o0, o1, o2)` on repetition `0`
    either:
    1. Carries a root attestation, accepted at the FIPS 204 message representative, of a message
       absent from `issuerSignedMessages signedLog`,
    2. Computes an explicit `H`-collision (`(vcRewoundCollisionFinder ...).isSome = true`),
    3. Exhibits a reachable rate-6/capacity-6 width-12 sponge collision, or
    4. Matches a credential `(attrs, holderBlind)` minted in some logged epoch `ep ∈ signedLog`.
    The three openings are a hypothesis; no prover is rewound here. -/
theorem blindVc_multi_epoch_signing_log_fresh_forgery
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {issuerA : PolyMat4} {issuerT1Scaled : PolyVec4} {issuerPk : List UInt8}
    {issuerPkDigest : Vec UInt8 32} {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {trusted : BlindVcTrustedContext} {expectedSchema : VcSchema} {treeDepth : Nat}
    {verifierChallenge : List UInt8} {rootSig : ThresholdSignSig} {pres : BlindVcPresentation}
    (signedLog : List (IssuerMintedEpoch expectedSchema treeDepth))
    (o0 o1 o2 : OpenedBlindVcRep)
    (hVer : verifyBlindVcWithIssuerAttestation chalHash sampleInBall issuerA issuerT1Scaled
      issuerPk issuerPkDigest H prgExpand trusted expectedSchema treeDepth verifierChallenge
      rootSig pres = true)
    (hRew01 : reconstructRepRound1 H pres.presentationNonce 0 o0 =
      reconstructRepRound1 H pres.presentationNonce 0 o1)
    (hRew12 : reconstructRepRound1 H pres.presentationNonce 0 o1 =
      reconstructRepRound1 H pres.presentationNonce 0 o2)
    (hRep0 : verifyOpenedBlindVcRep prgExpand expectedSchema pres.issuerEpoch treeDepth
      pres.accumulatorRoot pres.presCommit pres.scopeTag pres.verifierScopeLimbs
      pres.disclosedAttrs 0 0 o0 = true)
    (hRep1 : verifyOpenedBlindVcRep prgExpand expectedSchema pres.issuerEpoch treeDepth
      pres.accumulatorRoot pres.presCommit pres.scopeTag pres.verifierScopeLimbs
      pres.disclosedAttrs 0 1 o1 = true)
    (hRep2 : verifyOpenedBlindVcRep prgExpand expectedSchema pres.issuerEpoch treeDepth
      pres.accumulatorRoot pres.presCommit pres.scopeTag pres.verifierScopeLimbs
      pres.disclosedAttrs 0 2 o2 = true) :
    (verifyIssuerRootAttestation chalHash sampleInBall issuerA issuerT1Scaled issuerPk
       (trusted.attestationFields issuerPkDigest) rootSig = true ∧
     (trusted.attestationFields issuerPkDigest).message ∉ issuerSignedMessages signedLog) ∨
    (vcRewoundCollisionFinder H hHLen pres.presentationNonce 0 o0 o1 o2).isSome = true ∨
    (∃ (c₁ c₂ : Lane6 × Lane6 × Lane6) (r : Fin 3),
      Poseidon2Perm12Sponge6Collision (spongeTrace204 c₁ r) (spongeTrace204 c₂ r)) ∨
    (∃ ep ∈ signedLog, ∃ cred ∈ ep.mintedCreds, ∃ presBlind : Lane4,
      (pres.disclosedAttrs.map Prod.fst).Nodup ∧
      (∀ p ∈ pres.disclosedAttrs, p.1 < expectedSchema.arity ∧ cred.1[p.1]? = some p.2) ∧
      computeVcPoseidon2Commit expectedSchema cred.1 presBlind vcPresCommitTag = some pres.presCommit ∧
      computeVcScopeTag expectedSchema.schemaId cred.2 trusted.verifierScopeLimbs = pres.scopeTag) := by
  obtain ⟨hSigOk, hTrustedOk⟩ := verifyBlindVcWithIssuerAttestation_eq_true_iff.mp hVer
  rcases issuerRootAttestation_fresh_or_logged signedLog
      (trusted.attestationFields issuerPkDigest) with hFresh | ⟨ep, hEpMem, hFields⟩
  · exact Or.inl ⟨hSigOk, hFresh⟩
  · have hEpochEq : ep.epoch = trusted.issuerEpoch :=
      congrArg IssuerRootAttestationFields.issuerEpoch hFields
    have hRootEq : vcMerkleTreeRoot ep.epoch 0 ep.tree = trusted.accumulatorRoot :=
      congrArg IssuerRootAttestationFields.accumulatorRoot hFields
    cases hFind : vcRewoundCollisionFinder H hHLen pres.presentationNonce 0 o0 o1 o2 with
    | some _ => exact Or.inr (Or.inl rfl)
    | none =>
      have hNoConf : ¬ VcRewoundCommitConflict H pres.presentationNonce 0 o0 o1 o2 := by
        intro hc
        have hSome := vcRewoundCollisionFinder_isSome H hHLen pres.presentationNonce 0 o0 o1 o2
        rw [hFind, decide_eq_true hc] at hSome
        cases hSome
      obtain ⟨hPresRoot, _, hPresEp, hScopeEq, _⟩ := verifyBlindVcPresentationTrusted_context hTrustedOk
      rcases verifyOpenedBlindVcRep_extract3_finite_conflict hRew01 hRew12 hRep0 hRep1 hRep2
        with hConf | hWit
      · exact False.elim (hNoConf hConf)
      · obtain ⟨attrs, hb, pb, leaf, steps, hNodup, _, hDisc, hLeaf, hSLen, hMerkle, hPres, hScope⟩ := hWit
        rw [hPresEp, ← hEpochEq, hPresRoot, ← hRootEq] at hMerkle
        rcases vcMerkleTree_opening_sound ep.epoch ep.tree 0 leaf steps hSLen hMerkle
          with hLeafIn | hMkColl
        · obtain ⟨cred, hCredMem, hCredLeaf⟩ := ep.hLeaves leaf hLeafIn
          if hSameCred : (attrs, hb) = cred then
            rcases cred with ⟨cAttrs, cHb⟩
            injection hSameCred with hAEq hHbEq; subst hAEq hHbEq; rw [← hScopeEq]
            exact Or.inr (Or.inr (Or.inr ⟨ep, hEpMem, (attrs, hb), hCredMem, pb,
              hNodup, hDisc, hPres, hScope⟩))
          else
            have hTripleNe : (expectedSchema, attrs, hb) ≠ (expectedSchema, cred.1, cred.2) := by
              intro he; injection he with _ h2; injection h2 with ha hbEq
              exact hSameCred (Prod.ext ha hbEq)
            obtain ⟨r, hCol⟩ := blindVcReachableBinding204 expectedSchema expectedSchema
              attrs cred.1 hb cred.2 vcAttrCommitTag leaf hLeaf hCredLeaf hTripleNe
            exact Or.inr (Or.inr (Or.inl ⟨_, _, r, hCol⟩))
        · exact Or.inr (Or.inr (Or.inl hMkColl))

#verify_constructive
  findTritOpeningInLog_sound assembleThreeOpeningsFromLog_sound
  blindVcExtractCollisionOrWitness_sound assembleThreeOpeningsFromLog_extracts_collision_of_not_inLang
  issuerRootAttestation_fresh_or_logged issuerRootAttestationBytes_fresh_forgery_or_logged
  blindVc_multi_epoch_signing_log_fresh_forgery

end Qsag
