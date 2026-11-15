module

public import Qsag.BlindVcQromSecurity
import all Qsag.BlindVcQromSecurity
import all Qsag.ThresholdMlDsaAndToprf

/-!
Executable collision extraction, rate-6 / capacity-6 6-limb sponge coherence,
transcript-log 3-opening assembly, and multi-epoch issuer signing-log freshness
for `BlindVC`.
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
4. **Multi-Epoch Signing-Log Fresh-Message EUF-CMA Reduction
   (`encodeIssuerRootAttestationMsg_injective`,
   `blindVc_multi_epoch_signing_log_fresh_forgery`)**:
   Proves fixed-offset `97`-byte injectivity of `encodeIssuerRootAttestationMsg`
   and establishes that any unlogged root attestation accepted by `ML-DSA`
   verifies on a byte string strictly absent (`∉`) from `issuerSignedMessages signedLog`.
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
    (blindVcTableCollisionFinder H hHLen stmt msg).isSome = blindVcTableConflict H stmt msg :=
  blindVcCollisionScan_isSome H hHLen stmt msg (List.range k)

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

/-- The concrete conflicting-view construction returns an actual collision. -/
theorem vcRewoundCollisionFinder_constant_hash
    (nonce : Vec UInt8 32) (idx : Nat) (o : OpenedBlindVcRep) :
    let bad := { o with
      viewE := { o.viewE with attrShares := [] }
      viewE1 := { o.viewE with attrShares := [Goldilocks.zero] } }
    (vcRewoundCollisionFinder (fun _ => []) (by intro _; decide)
      nonce idx bad bad bad).isSome = true := by
  intro bad
  rw [vcRewoundCollisionFinder_isSome]
  exact decide_eq_true (vcRewoundCommitConflict_constant_hash nonce idx o)

#verify_constructive foldFramesHash_collision_of_ne vcCommitPartyView_binding
  vcRewoundCollisionFinder_isSome blindVcCollisionScan_isSome
  blindVcTableCollisionFinder_isSome blindVcCollisionReduction_mass
  blindVc_fs_collisionFinder_decomposition blindVc_fs_collisionFinder_mass_bound
  vcRewoundCollisionFinder_honest vcRewoundCollisionFinder_constant_hash


/-! ## §2. Rate-6 / Capacity-6 6-Limb Sponge Coherence, Log-Based 3-Opening Extraction & Multi-Epoch Signing-Log Freshness -/

set_option exponentiation.threshold 1024 in
/-- **Rate-6 / Capacity-6 Width-12 `sponge12` 6-Limb Coherence (`blindVc_sponge12_rate6_cap6_six_limb_coherence`)**:
    Locks `BlindVcCollisionFinder` directly to `crates/qsag-cred/src/blind_vc.rs:149-268`:
    1. `computeVcPoseidon2Commit` accepts iff `1 ≤ attrs.length = schema.arity ≤ 6`, absorbs `schema.arity`
       at `c2.x0` and `10*` pad `1` at `c2.x1` into the 3-block rate-6 / capacity-6 `absorbRate6Sponge3`
       (with 6 zero-initialized capacity lanes), and squeezes 6 limbs (`Lane6`, `> 2^383` states);
    2. `computeVcScopeTag` absorbs two 6-limb blocks plus the full-block `10*` pad `⟨1, 0, 0, 0, 0, 0⟩`
       (`N = 12` multiple of rate `6`) into `absorbRate6Sponge3` and squeezes 6 limbs (`Lane6`);
    3. `vcMerkleHashPair` absorbs left/right 6-limb child digests plus 4 domain limbs and `10*` pad `1`
       at `c2.x4` (`N = 16`) into `absorbRate6Sponge3` and squeezes 6 limbs (`Lane6`). -/
theorem blindVc_sponge12_rate6_cap6_six_limb_coherence
    (schema : VcSchema) (attrs : List Goldilocks) (blind scopeLimbs : Lane4)
    (tag epoch : UInt64) (left right : Lane6) (layer : Nat) :
    ((attrs.length = schema.arity →
        (vcCommitChunks schema attrs blind tag).2.2 =
          ⟨Goldilocks.ofNat schema.arity, Goldilocks.one,
           Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ ∧
        computeVcPoseidon2Commit schema attrs blind tag =
          some (state12Rate6 (absorbRate6Sponge3
            (vcCommitChunks schema attrs blind tag).1
            (vcCommitChunks schema attrs blind tag).2.1
            (vcCommitChunks schema attrs blind tag).2.2))) ∧
     (attrs.length ≠ schema.arity → computeVcPoseidon2Commit schema attrs blind tag = none)) ∧
    ((vcScopeChunks schema.schemaId blind scopeLimbs).2.2 =
        ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero,
         Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ ∧
     computeVcScopeTag schema.schemaId blind scopeLimbs =
        state12Rate6 (absorbRate6Sponge3
          (vcScopeChunks schema.schemaId blind scopeLimbs).1
          (vcScopeChunks schema.schemaId blind scopeLimbs).2.1
          (vcScopeChunks schema.schemaId blind scopeLimbs).2.2)) ∧
    ((vcMerkleChunks left right epoch layer).2.2.x4 = Goldilocks.one ∧
     (vcMerkleChunks left right epoch layer).2.2.x5 = Goldilocks.zero ∧
     vcMerkleHashPair left right epoch layer =
        state12Rate6 (absorbRate6Sponge3 left right
          (vcMerkleChunks left right epoch layer).2.2)) ∧
    state12Cap6 (mkState12Of6 (vcCommitChunks schema attrs blind tag).1 lane6Zero) = lane6Zero ∧
    2 ^ 383 < goldilocksPrime ^ 6 := by
  refine ⟨⟨fun hEq => ⟨rfl, ?_⟩, fun hNe => ?_⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, by decide⟩
  · unfold computeVcPoseidon2Commit; simp only [hEq, ↓reduceIte]
  · unfold computeVcPoseidon2Commit; simp only [hNe, ↓reduceIte]

private def vecOfListExact {α : Type} : (xs : List α) → {n : Nat} → xs.length = n → Vec α n
  | [], 0, _ => .nil
  | x :: xs, _ + 1, h => .cons x (vecOfListExact xs (Nat.succ.inj h))

private theorem vecOfListExact_toList {α : Type} : ∀ (xs : List α) {n : Nat} (h : xs.length = n),
    (vecOfListExact xs h).toList = xs
  | [], 0, _ => rfl
  | _ :: xs, _ + 1, h => by simp [vecOfListExact, Vec.toList, vecOfListExact_toList xs (Nat.succ.inj h)]

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
  simp only [verifyCommittedBlindVcRep, Bool.and_eq_true, decide_eq_true_eq] at h0 h1 h2
  rcases h0 with ⟨hR0, hV0⟩
  rcases h1 with ⟨hR1, hV1⟩
  rcases h2 with ⟨hR2, hV2⟩
  rcases verifyOpenedBlindVcRep_extract3_finite_conflict
      (hR1_01 := hR0.trans hR1.symm) (hR1_12 := hR1.trans hR2.symm) hV0 hV1 hV2 with hConf | hExt
  · exact False.elim (hNoConf hConf)
  · obtain ⟨attrs, hb, pb, leaf, steps, _, hAr, hDisc, hLeaf, hSLen, hRoot, hPres, hScope⟩ := hExt
    have hAsc : vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true := by
      unfold verifyOpenedBlindVcRep at hV0; dsimp only at hV0
      cases hG :
          (decide (o0.e = 0) &&
           vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs &&
           decide (o0.viewE.attrShares.length = stmt.schema.arity) &&
           decide (o0.viewE1.attrShares.length = stmt.schema.arity) &&
           decide (o0.viewE.merkleLevels.length = stmt.treeDepth) &&
           decide (o0.viewE1.merkleLevels.length = stmt.treeDepth) &&
           vcCheckPartyDisclosedShares o0.e o0.viewE.attrShares stmt.disclosedAttrs &&
           vcCheckPartyDisclosedShares (vcNextParty3 o0.e) o0.viewE1.attrShares stmt.disclosedAttrs &&
           checkPartyPrgTape prgExpand stmt.treeDepth repIdx o0.e o0.viewE &&
           checkPartyPrgTape prgExpand stmt.treeDepth repIdx (vcNextParty3 o0.e) o0.viewE1) with
      | false => rw [hG] at hV0; cases hV0
      | true => simp only [Bool.and_eq_true] at hG; exact hG.1.1.1.1.1.1.1.1.2
    refine ⟨{ attrs := vecOfListExact attrs hAr, holderBlind := hb, presBlind := pb,
              merkleSteps := vecOfListExact steps hSLen }, ?_⟩
    unfold BlindVcWitnessValid
    refine ⟨hAsc, fun p hp => ?_, ⟨leaf, ?_, ?_⟩, ?_, hScope⟩
    · rw [vecOfListExact_toList attrs hAr]; exact (hDisc p hp).2
    · rw [vecOfListExact_toList attrs hAr]; exact hLeaf
    · rw [vecOfListExact_toList steps hSLen]; exact hRoot
    · rw [vecOfListExact_toList attrs hAr]; exact hPres

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

/-- Fixed-offset `97`-byte injectivity of `encodeIssuerRootAttestationMsg`
    (`9`-byte `"QSAG.ROOT"` + `32`-byte `issuerRootTag` + `8`-byte `epoch` + `48`-byte `Lane6` root). -/
theorem encodeIssuerRootAttestationMsg_injective
    {tag₁ tag₂ : Vec UInt8 32} {ep₁ ep₂ : UInt64} {root₁ root₂ : Lane6}
    (hEq : encodeIssuerRootAttestationMsg tag₁ ep₁ root₁ =
           encodeIssuerRootAttestationMsg tag₂ ep₂ root₂) :
    tag₁ = tag₂ ∧ ep₁ = ep₂ ∧ root₁ = root₂ := by
  unfold encodeIssuerRootAttestationMsg at hEq
  simp only [List.append_assoc] at hEq
  have hPfxLen : ([0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x4F, 0x4F, 0x54] : List UInt8).length =
      ([0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x4F, 0x4F, 0x54] : List UInt8).length := rfl
  obtain ⟨_, hRest1⟩ := append_inj_of_eq_len hPfxLen hEq
  have hTagLen : tag₁.toList.length = tag₂.toList.length := by
    rw [Vec.toList_length, Vec.toList_length]
  obtain ⟨hTagBytes, hRest2⟩ := append_inj_of_eq_len hTagLen hRest1
  have hEpLen : (encodeNatLeBytes 8 ep₁.toNat).length = (encodeNatLeBytes 8 ep₂.toNat).length := by
    rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
  obtain ⟨hEpBytes, hRootBytes⟩ := append_inj_of_eq_len hEpLen hRest2
  have hTagEq : tag₁ = tag₂ := Vec.toList_injective hTagBytes
  have hEp1Lt : ep₁.toNat < 256 ^ 8 := by
    have h := ep₁.toNat_lt_size; change ep₁.toNat < 18446744073709551616 at h; omega
  have hEp2Lt : ep₂.toNat < 256 ^ 8 := by
    have h := ep₂.toNat_lt_size; change ep₂.toNat < 18446744073709551616 at h; omega
  have hEpNat : ep₁.toNat = ep₂.toNat := by
    have hd := congrArg decodeNatLeBytes hEpBytes
    rwa [decodeNatLeBytes_encodeNatLeBytes 8 ep₁.toNat hEp1Lt,
         decodeNatLeBytes_encodeNatLeBytes 8 ep₂.toNat hEp2Lt] at hd
  have hEpEq : ep₁ = ep₂ := UInt64.toNat_inj.mp hEpNat
  have hLimbs := encodeGoldilocksVecLe_injective hRootBytes
  simp only [List.cons.injEq] at hLimbs
  rcases hLimbs with ⟨e0, e1, e2, e3, e4, e5, _⟩
  exact ⟨hTagEq, hEpEq, Lane6.ext e0 e1 e2 e3 e4 e5⟩

/-- **`#tooth` (`tooth_unframed_varlen_tag_epoch_alias`)**:
    Without fixed `32`-byte `Vec UInt8 32` framing on `issuerRootTag`, variable-length concatenation
    `tag ++ encodeNatLeBytes 8 epoch.toNat` aliases `([0x41, 0x00], 0)` with `([0x41], 0)` + `[0x00]`
    boundary shift (distinct variable-length prefixes producing identical signed message bytes). -/
theorem tooth_unframed_varlen_tag_epoch_alias (tag₁ tag₂ : Vec UInt8 32) (hNe : tag₁ ≠ tag₂) :
    ∃ (t₁ t₂ : List UInt8) (ep₁ ep₂ : UInt64),
      (t₁, ep₁) ≠ (t₂, ep₂) ∧
      t₁ ++ encodeNatLeBytes 8 ep₁.toNat = (t₂ ++ [0x00]) ++ encodeNatLeBytes 8 ep₂.toNat ∧
      encodeIssuerRootAttestationMsg tag₁ 0 lane6Zero ≠
        encodeIssuerRootAttestationMsg tag₂ 0 lane6Zero :=
  ⟨[0x41, 0x00], [0x41], 0, 0, by decide, rfl,
   fun hEq => hNe (encodeIssuerRootAttestationMsg_injective hEq).1⟩

/-- Exact list of root-attestation byte messages signed by the issuer across a multi-epoch log. -/
def issuerSignedMessages {schema : VcSchema} {treeDepth : Nat}
    (signedLog : List (IssuerMintedEpoch schema treeDepth)) : List (List UInt8) :=
  signedLog.map (fun ep =>
    encodeIssuerRootAttestationMsg ep.issuerRootTag ep.epoch (vcMerkleTreeRoot ep.epoch 0 ep.tree))

private def findMatchingLoggedEpoch {schema : VcSchema} {treeDepth : Nat}
    (tag : Vec UInt8 32) (epoch : UInt64) (accRoot : Lane6) :
    List (IssuerMintedEpoch schema treeDepth) → Option (IssuerMintedEpoch schema treeDepth)
  | [] => none
  | ep :: rest =>
    if decide (ep.issuerRootTag = tag ∧ ep.epoch = epoch ∧ vcMerkleTreeRoot ep.epoch 0 ep.tree = accRoot) then
      some ep
    else
      findMatchingLoggedEpoch tag epoch accRoot rest

private theorem findMatchingLoggedEpoch_some {schema : VcSchema} {treeDepth : Nat}
    {tag : Vec UInt8 32} {epoch : UInt64} {accRoot : Lane6} :
    ∀ {log : List (IssuerMintedEpoch schema treeDepth)} {ep : IssuerMintedEpoch schema treeDepth},
      findMatchingLoggedEpoch tag epoch accRoot log = some ep →
      ep ∈ log ∧ ep.issuerRootTag = tag ∧ ep.epoch = epoch ∧
      vcMerkleTreeRoot ep.epoch 0 ep.tree = accRoot
  | [], _, h => by cases h
  | hd :: rest, ep, h => by
    unfold findMatchingLoggedEpoch at h
    cases hDec : decide (hd.issuerRootTag = tag ∧ hd.epoch = epoch ∧ vcMerkleTreeRoot hd.epoch 0 hd.tree = accRoot) with
    | true =>
      rw [hDec] at h; simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      have hCond := of_decide_eq_true hDec
      exact ⟨.head rest, hCond.1, hCond.2.1, hCond.2.2⟩
    | false =>
      rw [hDec] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hMem, h1, h2, h3⟩ := findMatchingLoggedEpoch_some h
      exact ⟨.tail hd hMem, h1, h2, h3⟩

private theorem findMatchingLoggedEpoch_none_not_mem_signedMessages
    {schema : VcSchema} {treeDepth : Nat}
    {tag : Vec UInt8 32} {epoch : UInt64} {accRoot : Lane6} :
    ∀ {log : List (IssuerMintedEpoch schema treeDepth)},
      findMatchingLoggedEpoch tag epoch accRoot log = none →
      encodeIssuerRootAttestationMsg tag epoch accRoot ∉ issuerSignedMessages log
  | [], _, hMem => nomatch hMem
  | hd :: rest, hNone, hMem => by
    unfold findMatchingLoggedEpoch at hNone
    cases hDec : decide (hd.issuerRootTag = tag ∧ hd.epoch = epoch ∧ vcMerkleTreeRoot hd.epoch 0 hd.tree = accRoot) with
    | true =>
      rw [hDec] at hNone; simp only [↓reduceIte] at hNone
      cases hNone
    | false =>
      rw [hDec] at hNone; simp only [Bool.false_eq_true, ↓reduceIte] at hNone
      have hNotCond := of_decide_eq_false hDec
      unfold issuerSignedMessages at hMem
      simp only [List.map_cons, List.mem_cons] at hMem
      rcases hMem with hEqMsg | hInRest
      · obtain ⟨eTag, eEp, eRoot⟩ := encodeIssuerRootAttestationMsg_injective hEqMsg.symm
        exact hNotCond ⟨eTag, eEp, eRoot⟩
      · exact findMatchingLoggedEpoch_none_not_mem_signedMessages hNone hInRest

/-- **Multi-Epoch Signing-Log Fresh-Message EUF-CMA & Collision Reduction
    (`blindVc_multi_epoch_signing_log_fresh_forgery`)**:
    Upgrades single-epoch `blindVc_presentation_reduces_to_issuer_mldsa` to an arbitrary multi-epoch
    issuer signing log `signedLog : List (IssuerMintedEpoch expectedSchema treeDepth)`:
    any accepted presentation with 3 rewound/logged openings `(o0, o1, o2)` on repetition `0` either:
    1. Produces a valid `ML-DSA` signature on `msgBytes` **strictly absent (`∉`) from the entire
       multi-epoch signing log `issuerSignedMessages signedLog`** (genuine fresh-message EUF-CMA forgery),
    2. Computes an explicit `H`-collision (`(vcRewoundCollisionFinder ...).isSome = true`),
    3. Exhibits a reachable rate-6/capacity-6 width-12 sponge collision (`Poseidon2Perm12Sponge6Collision`), or
    4. Matches an authentic credential `(attrs, holderBlind)` minted in some logged epoch `ep ∈ signedLog`. -/
theorem blindVc_multi_epoch_signing_log_fresh_forgery
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {issuerA : PolyMat4} {issuerT1Scaled : PolyVec4} {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {trusted : BlindVcTrustedContext} {expectedSchema : VcSchema} {treeDepth : Nat}
    {verifierChallenge : List UInt8} {rootSig : ThresholdSignSig} {pres : BlindVcPresentation}
    (signedLog : List (IssuerMintedEpoch expectedSchema treeDepth))
    (o0 o1 o2 : OpenedBlindVcRep)
    (hVer : verifyBlindVcWithIssuerAttestation chalHash sampleInBall issuerA issuerT1Scaled
      H prgExpand trusted expectedSchema treeDepth verifierChallenge rootSig pres = true)
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
    let msgBytes := encodeIssuerRootAttestationMsg
      trusted.issuerRootTag trusted.issuerEpoch trusted.accumulatorRoot
    (mldsaVerify chalHash sampleInBall issuerA issuerT1Scaled
       msgBytes rootSig.cTilde rootSig.z rootSig.h = true ∧
     msgBytes ∉ issuerSignedMessages signedLog) ∨
    (vcRewoundCollisionFinder H hHLen pres.presentationNonce 0 o0 o1 o2).isSome = true ∨
    (∃ (c₁ c₂ : Lane6 × Lane6 × Lane6) (r : Fin 3),
      Poseidon2Perm12Sponge6Collision (spongeTrace204 c₁ r) (spongeTrace204 c₂ r)) ∨
    (∃ ep ∈ signedLog, ∃ cred ∈ ep.mintedCreds, ∃ presBlind : Lane4,
      (pres.disclosedAttrs.map Prod.fst).Nodup ∧
      (∀ p ∈ pres.disclosedAttrs, p.1 < expectedSchema.arity ∧ cred.1[p.1]? = some p.2) ∧
      computeVcPoseidon2Commit expectedSchema cred.1 presBlind vcPresCommitTag = some pres.presCommit ∧
      computeVcScopeTag expectedSchema.schemaId cred.2 trusted.verifierScopeLimbs = pres.scopeTag) := by
  intro msgBytes
  cases hMatch : findMatchingLoggedEpoch
      trusted.issuerRootTag trusted.issuerEpoch trusted.accumulatorRoot signedLog with
  | none =>
    unfold verifyBlindVcWithIssuerAttestation at hVer
    rw [Bool.and_eq_true] at hVer
    exact Or.inl ⟨hVer.1, findMatchingLoggedEpoch_none_not_mem_signedMessages hMatch⟩
  | some ep =>
    obtain ⟨hEpMem, hTagEq, hEpochEq, hRootEq⟩ := findMatchingLoggedEpoch_some hMatch
    cases hFind : vcRewoundCollisionFinder H hHLen pres.presentationNonce 0 o0 o1 o2 with
    | some _ => exact Or.inr (Or.inl rfl)
    | none =>
      have hNoConf : ¬ VcRewoundCommitConflict H pres.presentationNonce 0 o0 o1 o2 := by
        intro hc
        have hSome := vcRewoundCollisionFinder_isSome H hHLen pres.presentationNonce 0 o0 o1 o2
        rw [hFind, decide_eq_true hc] at hSome
        cases hSome
      unfold verifyBlindVcWithIssuerAttestation at hVer
      rw [Bool.and_eq_true] at hVer
      obtain ⟨_, hTrustedOk⟩ := hVer
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

#verify_constructive blindVc_sponge12_rate6_cap6_six_limb_coherence
  findTritOpeningInLog_sound assembleThreeOpeningsFromLog_sound
  blindVcExtractCollisionOrWitness_sound assembleThreeOpeningsFromLog_extracts_collision_of_not_inLang
  encodeIssuerRootAttestationMsg_injective tooth_unframed_varlen_tag_epoch_alias
  blindVc_multi_epoch_signing_log_fresh_forgery
#tooth_pair encodeIssuerRootAttestationMsg_injective vs tooth_unframed_varlen_tag_epoch_alias

end Qsag
