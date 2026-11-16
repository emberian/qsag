module
/-
# BlindVC ternary (3-party ZKBoo, 438 repetitions) model and issuer root attestation

`blind_vc.rs` uses 3-party ZKBoo with 438 repetitions for blind issuance; its presentations
are the 256-party, 33-repetition protocol over `GF(p^5)`, modelled in
`AdvancedMpcAndCreds` (seed tree, hidden-party opening) and counted in
`RepetitionCutAndChoose`. The `BlindVcPresentation` / `BlindVcPublicStatement` relation of
this module (disclosed attributes, Merkle membership, scope tag, proved by ternary openings) is
the ZKBoo presentation that protocol replaced: sections 1 and 2 are statements about that
ternary model, not about deployed presentations.

1. **Ternary parallel repetition (`blindVcParallelRbr`,
   `blindVc_quantum128_interactive_rbr_bound`)**: for the collision-filtered,
   supplied-opening-table verifier, at most `2^438` of `3^438` challenge vectors accept a false
   statement (`2^438 * 2^256 < 3^438`), composed with `rbr_implies_state_restoration_soundness`.
   `VcRewoundCommitConflict` is the event the filter removes;
   `blindVc_committed_acceptance_decomposition` accounts for it. Bounding that event, building
   the three-opening table from a quantum prover and linking measured-query mass to forgery are
   not done here.
2. **Ternary QROM round (`blindVcQromFsRound`, `blindVc_quantum128_qrom_fs_soundness`)**:
   exact `64`-bit modulo-`3` squeeze (`blindVcBadWord64` of `2^64`) and
   `(2Q + 1)^2 * blindVcBadWord64^438 * 2^128 < (2^64)^438` for `Q ≤ 2^60`.
3. **Merkle path bridge and issuer root attestation** (shared by both presentation protocols):
   `evalVcMerklePathBool_eq_merkleRootFromPath`, `vcMerkleTree_opening_sound`; the attestation
   message `IssuerRootAttestation::signing_message` (142 bytes, injective), the FIPS 204
   message representative `μ = SHAKE256(SHAKE256(pk, 64) ‖ 0 ‖ |ctx| ‖ ctx ‖ M, 64)`
   (`fips204MessageRepresentative`), the attestation check on the algebraic ML-DSA core at `μ`
   (`verifyIssuerRootAttestation`) and on wire bytes (`verifyIssuerRootAttestationBytes`,
   `verifyIssuerRootAttestationBytes_accepts_core`), and
   `blindVc_presentation_reduces_to_issuer_mldsa` for the ternary model. EUF-CMA of ML-DSA and
   quantum extraction are separate games.
4. **Opening round of the 256-party presentation in the QROM**
   (`credentialSd_opening_bad_count_le_one`, `credentialSd_opening_round_qrom_bound`): the
   33-byte hidden-party challenge alone, conditional on a nonzero check value per repetition.
-/

public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

set_option exponentiation.threshold 2048

private theorem nat_lt_of_mul_lt_mul_right {a b c : Nat} (h : a * c < b * c) : a < b :=
  if hab : a < b then hab
  else False.elim (Nat.lt_irrefl (b * c)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right c (Nat.le_of_not_lt hab)) h))

private theorem dite_true {α : Sort _} {P : Prop} [Decidable P] (h : P)
    (t : P → α) (e : ¬ P → α) : (if hp : P then t hp else e hp) = t h := by
  cases ‹Decidable P› with | isTrue _ => rfl | isFalse hnp => exact absurd h hnp

private theorem ite_true {α : Sort _} {P : Prop} [Decidable P] (h : P) (a b : α) :
    (if P then a else b) = a := by
  cases ‹Decidable P› with | isTrue _ => rfl | isFalse hnp => exact absurd h hnp

private theorem ite_false {α : Sort _} {P : Prop} [Decidable P] (h : ¬ P) (a b : α) :
    (if P then a else b) = b := by
  cases ‹Decidable P› with | isTrue hp => exact absurd hp h | isFalse _ => rfl

private theorem qsum_cast {n m : Nat} (h : n = m) (f : Fin n → Nat) :
    qsum n f = qsum m (fun k => f ⟨k.1, h ▸ k.2⟩) := by
  subst h; exact qsum_congr (fun ⟨_, _⟩ => rfl)

def Vec.get {α : Type} : {n : Nat} → Vec α n → Fin n → α
  | _ + 1, .cons x _, ⟨0, _⟩ => x
  | _ + 1, .cons _ xs, ⟨i + 1, hi⟩ => Vec.get xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩

def vecOfListLen {α : Type} : (xs : List α) → {n : Nat} → xs.length = n → Vec α n
  | [], 0, _ => .nil
  | x :: xs, _ + 1, h => .cons x (vecOfListLen xs (Nat.succ.inj h))

theorem vecOfListLen_toList {α : Type} : ∀ (xs : List α) {n : Nat} (h : xs.length = n),
    (vecOfListLen xs h).toList = xs
  | [], 0, _ => by rw [vecOfListLen, Vec.toList_nil]
  | _ :: xs, _ + 1, h => by
    rw [vecOfListLen, Vec.toList_cons, vecOfListLen_toList xs (Nat.succ.inj h)]

/-! ## §1. `438`-Repetition `BlindVC` ZKBoo `PublicCoinIop` & `RbrStateFunction` -/

def fin3AllTrue (p : Fin 3 → Bool) : Bool := p 0 && p 1 && p 2

theorem fin3_not_all_count_le_two (p : Fin 3 → Bool)
    (hNotAll : fin3AllTrue p = false) :
    qsum 3 (fun e => if p e = true then 1 else 0) ≤ 2 := by
  unfold fin3AllTrue at hNotAll
  simp only [qsum_succ, qsum_zero, Nat.add_zero]
  change (if p 0 = true then 1 else 0) +
    ((if p 1 = true then 1 else 0) + (if p 2 = true then 1 else 0)) ≤ 2
  cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : p 2 <;> simp_all

def verifyCommittedBlindVcRep
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement) (repIdx : Nat)
    (r1 : Triple3 (List UInt8) × VcRepFinalOuts3) (e : Fin 3) (o : OpenedBlindVcRep) : Bool :=
  decide (reconstructRepRound1 H stmt.presNonce repIdx o = r1) &&
  verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
    stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
    stmt.disclosedAttrs repIdx e o

theorem verifyCommittedBlindVcRep_eq_true_iff
    {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {stmt : BlindVcPublicStatement} {repIdx : Nat}
    {r1 : Triple3 (List UInt8) × VcRepFinalOuts3} {e : Fin 3} {o : OpenedBlindVcRep} :
    verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 e o = true ↔
      (reconstructRepRound1 H stmt.presNonce repIdx o = r1 ∧
       verifyOpenedBlindVcRep prgExpand stmt.schema stmt.issuerEpoch stmt.treeDepth
         stmt.accumulatorRoot stmt.presCommit stmt.scopeTag stmt.verifierScopeLimbs
         stmt.disclosedAttrs repIdx e o = true) := by
  unfold verifyCommittedBlindVcRep
  rw [Bool.and_eq_true, decide_eq_true_eq]

/-- Excludes only a collision in this supplied three-opening table. The unfiltered
verifier remains `verifyCommittedBlindVcRep`; the omitted event is accounted for below. -/
def verifyCollisionFreeCommittedBlindVcRep
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement) (repIdx : Nat)
    (r1 : Triple3 (List UInt8) × VcRepFinalOuts3)
    (cand : Fin 3 → OpenedBlindVcRep) (e : Fin 3) : Bool :=
  !decide (VcRewoundCommitConflict H stmt.presNonce repIdx (cand 0) (cand 1) (cand 2)) &&
    verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 e (cand e)

/-- Exact event decomposition: any omitted acceptance supplies a concrete pair of
conflicting committed views. No global collision-freedom premise is used. -/
theorem blindVc_committed_acceptance_decomposition
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement) (repIdx : Nat)
    (r1 : Triple3 (List UInt8) × VcRepFinalOuts3)
    (cand : Fin 3 → OpenedBlindVcRep) (e : Fin 3)
    (h : verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 e (cand e) = true) :
    VcRewoundCommitConflict H stmt.presNonce repIdx (cand 0) (cand 1) (cand 2) ∨
    verifyCollisionFreeCommittedBlindVcRep H prgExpand stmt repIdx r1 cand e = true := by
  by_cases hc : VcRewoundCommitConflict H stmt.presNonce repIdx (cand 0) (cand 1) (cand 2)
  · exact Or.inl hc
  · exact Or.inr (by simp only [verifyCollisionFreeCommittedBlindVcRep, hc, decide_false,
      Bool.not_false, Bool.true_and, h])

/-- The data extracted from three consistent openings is a valid witness of the statement. -/
theorem blindVcWitnessValid_of_extraction {stmt : BlindVcPublicStatement}
    {attrs : List Goldilocks} {hb pb : Lane4} {leaf : Lane6} {steps : List (Bool × Lane6)}
    (hAsc : vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true)
    (hAr : attrs.length = stmt.schema.arity) (hSLen : steps.length = stmt.treeDepth)
    (hDisc : ∀ p ∈ stmt.disclosedAttrs, attrs[p.1]? = some p.2)
    (hLeaf : computeVcPoseidon2Commit stmt.schema attrs hb vcAttrCommitTag = some leaf)
    (hRoot : evalVcMerklePathBool stmt.issuerEpoch 0 leaf steps = stmt.accumulatorRoot)
    (hPres : computeVcPoseidon2Commit stmt.schema attrs pb vcPresCommitTag = some stmt.presCommit)
    (hScope : computeVcScopeTag stmt.schema.schemaId hb stmt.verifierScopeLimbs = stmt.scopeTag) :
    ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth, BlindVcWitnessValid stmt wit := by
  refine ⟨{ attrs := vecOfListLen attrs hAr, holderBlind := hb, presBlind := pb,
            merkleSteps := vecOfListLen steps hSLen }, ?_⟩
  rw [blindVcWitnessValid_iff]
  refine ⟨hAsc, fun p hp => ?_, ⟨leaf, ?_, ?_⟩, ?_, hScope⟩
  · rw [vecOfListLen_toList attrs hAr]; exact hDisc p hp
  · rw [vecOfListLen_toList attrs hAr]; exact hLeaf
  · rw [vecOfListLen_toList steps hSLen]; exact hRoot
  · rw [vecOfListLen_toList attrs hAr]; exact hPres

/-- **Per-Repetition 3-Challenge Pigeonhole Soundness (`blindVc_rep_pigeonhole_le_two`)**:
    On a false statement, at most `2` of `3` collision-filtered challenges accept. -/
private theorem blindVc_rep_pigeonhole_core
    {H : List UInt8 → List UInt8} (_hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {stmt : BlindVcPublicStatement}
    (hNoWit : ¬ ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth,
      BlindVcWitnessValid stmt wit)
    (repIdx : Nat) (r1 : Triple3 (List UInt8) × VcRepFinalOuts3)
    (cand : Fin 3 → OpenedBlindVcRep)
    (hNoColl : ¬ VcRewoundCommitConflict H stmt.presNonce repIdx (cand 0) (cand 1) (cand 2)) :
    qsum 3 (fun e =>
      if verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 e (cand e) = true then 1 else 0) ≤ 2 := by
  apply fin3_not_all_count_le_two; unfold fin3AllTrue
  cases hAll :
      (verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 0 (cand 0) &&
       verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 1 (cand 1) &&
       verifyCommittedBlindVcRep H prgExpand stmt repIdx r1 2 (cand 2)) with
  | false => rfl
  | true =>
    simp only [verifyCommittedBlindVcRep, Bool.and_eq_true, decide_eq_true_eq] at hAll
    rcases hAll with ⟨⟨⟨hR0, hV0⟩, ⟨hR1, hV1⟩⟩, ⟨hR2, hV2⟩⟩
    rcases verifyOpenedBlindVcRep_extract3_finite_conflict
        (hR0.trans hR1.symm) (hR1.trans hR2.symm) hV0 hV1 hV2 with hColl | hExt
    · exact False.elim (hNoColl hColl)
    · obtain ⟨attrs, hb, pb, leaf, steps, _, hAr, hDisc, hLeaf, hSLen, hRoot, hPres, hScope⟩ := hExt
      exact False.elim (hNoWit (blindVcWitnessValid_of_extraction
        (verifyOpenedBlindVcRep_disclosedStrictAsc hV0) hAr hSLen
        (fun p hp => (hDisc p hp).2) hLeaf hRoot hPres hScope))

theorem blindVc_rep_pigeonhole_le_two
    {H : List UInt8 → List UInt8} (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {stmt : BlindVcPublicStatement}
    (hNoWit : ¬ ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth,
      BlindVcWitnessValid stmt wit)
    (repIdx : Nat) (r1 : Triple3 (List UInt8) × VcRepFinalOuts3)
    (cand : Fin 3 → OpenedBlindVcRep) :
    qsum 3 (fun e =>
      if verifyCollisionFreeCommittedBlindVcRep H prgExpand stmt repIdx r1 cand e = true then 1 else 0) ≤ 2 := by
  by_cases hc : VcRewoundCommitConflict H stmt.presNonce repIdx (cand 0) (cand 1) (cand 2)
  · simp only [verifyCollisionFreeCommittedBlindVcRep, hc, decide_true, Bool.not_true,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]
    exact Nat.zero_le 2
  · simp only [verifyCollisionFreeCommittedBlindVcRep, hc, decide_false, Bool.not_false,
      Bool.true_and]
    exact blindVc_rep_pigeonhole_core hHLen hNoWit repIdx r1 cand hc

def decodeTernaryChallengeAt (ch idx : Nat) : Fin 3 :=
  ⟨(ch / (3 ^ idx)) % 3, Nat.mod_lt _ (by decide)⟩

private theorem qsum_add_split_local :
    ∀ (X Y : Nat) (g : Fin (X + Y) → Nat),
      qsum (X + Y) g =
        qsum X (fun x => g ⟨x.1, by omega⟩) + qsum Y (fun y => g ⟨X + y.1, by omega⟩)
  | 0, Y, g => by
    rw [qsum_cast (Nat.zero_add Y) g]; simp only [qsum_zero, Nat.zero_add]
  | X + 1, Y, g => by
    have hEq : X + 1 + Y = (X + Y) + 1 := by omega
    rw [qsum_cast hEq g]
    have ih := qsum_add_split_local X Y (fun z => g ⟨z.1 + 1, by omega⟩)
    simp only [qsum_succ]
    have hTail : qsum Y (fun y => g ⟨X + y.1 + 1, by omega⟩) =
        qsum Y (fun y => g ⟨X + 1 + y.1, by omega⟩) :=
      qsum_congr (fun y => by congr 1; apply Fin.ext; dsimp only; omega)
    rw [ih, hTail]; exact (Nat.add_assoc _ _ _).symm

private theorem qsum_mul_factor :
    ∀ (A B : Nat) (f : Fin (A * B) → Nat),
      qsum (A * B) f =
        qsum A (fun i => qsum B (fun j =>
          f ⟨i.1 * B + j.1, by
            have h1 : (i.1 + 1) * B ≤ A * B := Nat.mul_le_mul_right B i.isLt
            have hj := j.isLt; rw [Nat.add_mul, Nat.one_mul] at h1; omega⟩))
  | 0, B, f => by rw [qsum_cast (Nat.zero_mul B) f, qsum_zero, qsum_zero]
  | A + 1, B, f => by
    have hAB : (A + 1) * B = B + A * B := by rw [Nat.succ_mul, Nat.add_comm]
    rw [qsum_cast hAB f, qsum_add_split_local B (A * B),
        qsum_mul_factor A B (fun k => f ⟨B + k.1, by omega⟩)]
    conv => rhs; rw [qsum_succ]
    congr 1
    · exact qsum_congr (fun j => by congr 1; apply Fin.ext; dsimp only; omega)
    · refine qsum_congr (fun i => qsum_congr (fun j => ?_))
      congr 1; apply Fin.ext; dsimp only
      rw [Nat.succ_mul, Nat.add_comm (i.1 * B) B, Nat.add_assoc]

/-- Product bound over `k` repetitions (`≤ B` of `M` per repetition `=> ≤ B^k` of `M^k`). -/
theorem product_bad_count_le_pow (M B : Nat) :
    ∀ (k : Nat) (p : Nat → Fin M → Bool),
      (∀ idx < k, qsum M (fun u => if p idx u = true then 1 else 0) ≤ B) →
      qsum (M ^ k) (fun ch =>
        if (List.range k).all
            (fun idx => if hM : 0 < M then p idx ⟨(ch.1 / (M ^ idx)) % M, Nat.mod_lt _ hM⟩ else false) = true
        then 1 else 0) ≤ B ^ k
  | 0, _, _ => by
    rw [qsum_cast (Nat.pow_zero M), qsum_succ, qsum_zero]
    exact Nat.le_refl 1
  | k + 1, p, hEach => by
    if hM0 : M = 0 then
      subst hM0; rw [qsum_cast (Nat.zero_pow (Nat.succ_pos k)), qsum_zero]; exact Nat.zero_le _
    else
      have hM : 0 < M := Nat.pos_of_ne_zero hM0
      rw [qsum_cast (Nat.pow_succ M k), qsum_mul_factor (M ^ k) M]
      have hFactor : ∀ (hi : Fin (M ^ k)) (lo : Fin M),
          (List.range (k + 1)).all
            (fun idx => if hM' : 0 < M then p idx ⟨((hi.1 * M + lo.1) / (M ^ idx)) % M, Nat.mod_lt _ hM'⟩
              else false) =
          (p 0 lo && (List.range k).all
            (fun idx => if hM' : 0 < M then p (idx + 1) ⟨(hi.1 / (M ^ idx)) % M, Nat.mod_lt _ hM'⟩
              else false)) := by
        intro hi lo; rw [List.range_succ_eq_map, List.all_cons, List.all_map]; congr 1
        · rw [dite_true hM]
          have hMod : (hi.1 * M + lo.1) % M = lo.1 := by
            rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt lo.isLt]
          have hFin : (⟨((hi.1 * M + lo.1) / M ^ 0) % M, Nat.mod_lt _ hM⟩ : Fin M) = lo := by
            apply Fin.ext; dsimp only [Nat.pow_zero]; rw [Nat.div_one, hMod]
          rw [hFin]
        · congr 1; funext idx; dsimp only [Function.comp]
          rw [dite_true hM, dite_true hM]; congr 1; apply Fin.ext; dsimp only
          have hDivM : (hi.1 * M + lo.1) / M = hi.1 := by
            rw [Nat.mul_comm, Nat.mul_add_div hM, Nat.div_eq_of_lt lo.isLt, Nat.add_zero]
          rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, hDivM]
      have hInner : ∀ hi : Fin (M ^ k),
          qsum M (fun lo =>
            if (List.range (k + 1)).all
                (fun idx => if hM' : 0 < M then p idx ⟨((hi.1 * M + lo.1) / (M ^ idx)) % M, Nat.mod_lt _ hM'⟩
                  else false) = true then 1 else 0) ≤
          (if (List.range k).all
                (fun idx => if hM' : 0 < M then p (idx + 1) ⟨(hi.1 / (M ^ idx)) % M, Nat.mod_lt _ hM'⟩
                  else false) = true then B else 0) := by
        intro hi; rw [qsum_congr (fun lo => by rw [hFactor hi lo])]
        cases (List.range k).all
            (fun idx => if hM' : 0 < M then p (idx + 1) ⟨(hi.1 / (M ^ idx)) % M, Nat.mod_lt _ hM'⟩ else false) with
        | false => simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero]; exact Nat.le_refl 0
        | true => simp only [Bool.and_true, ↓reduceIte]; exact hEach 0 (Nat.zero_lt_succ k)
      have hStep1 := qsum_le_qsum hInner
      have hMulB : qsum (M ^ k) (fun hi =>
          if (List.range k).all
              (fun idx => if hM' : 0 < M then p (idx + 1) ⟨(hi.1 / (M ^ idx)) % M, Nat.mod_lt _ hM'⟩ else false) = true
          then B else 0) =
        B * qsum (M ^ k) (fun hi =>
          if (List.range k).all
              (fun idx => if hM' : 0 < M then p (idx + 1) ⟨(hi.1 / (M ^ idx)) % M, Nat.mod_lt _ hM'⟩ else false) = true
          then 1 else 0) := by
        rw [← qsum_mul_left]; apply qsum_congr; intro hi
        cases (List.range k).all
          (fun idx => if hM' : 0 < M then p (idx + 1) ⟨(hi.1 / (M ^ idx)) % M, Nat.mod_lt _ hM'⟩ else false) <;>
          simp [Nat.mul_zero, Nat.mul_one]
      rw [hMulB] at hStep1
      have ih := product_bad_count_le_pow M B k (fun idx u => p (idx + 1) u)
        (fun idx hlt => hEach (idx + 1) (Nat.succ_lt_succ hlt))
      have hBPow : B * B ^ k = B ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.le_trans hStep1 (hBPow ▸ Nat.mul_le_mul_left B ih)

structure BlindVcParallelMsg (k : Nat) where
  allRound1 : Vec (Triple3 (List UInt8) × VcRepFinalOuts3) k
  openTable : Vec (Triple3 OpenedBlindVcRep) k
  deriving DecidableEq

def blindVcParallelIop
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (k : Nat) : PublicCoinIop BlindVcPublicStatement (BlindVcParallelMsg k) 1 where
  challengeCard := fun _ => 3 ^ k
  h_chal_pos := fun _ => Nat.pow_pos (by decide)
  inLang := fun stmt =>
    ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth, BlindVcWitnessValid stmt wit
  verify := fun stmt tr =>
    match tr with
    | [(msg, ch)] =>
      (List.range k).all (fun idx =>
        if hIdx : idx < k then
          let fi : Fin k := ⟨idx, hIdx⟩
          let e := decodeTernaryChallengeAt ch idx
          verifyCollisionFreeCommittedBlindVcRep H prgExpand stmt idx (Vec.get msg.allRound1 fi)
            (Vec.get msg.openTable fi).get e
        else true)
    | _ => false

/-- **Round-by-Round State Function (`blindVcParallelRbr`)** (`badCard 0 = 2^k` out of `3^k`). -/
def blindVcParallelRbr
    {H : List UInt8 → List UInt8} (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (k : Nat) : RbrStateFunction (blindVcParallelIop H prgExpand k) where
  Live := fun stmt tr =>
    match tr with
    | [] => (blindVcParallelIop H prgExpand k).inLang stmt
    | _ => (blindVcParallelIop H prgExpand k).verify stmt tr = true
  badCard := fun _ => 2 ^ k
  doomed_init := fun _ h => h
  accept_implies_live := fun _ tr hLen hVer => by cases tr with | nil => cases hLen | cons _ _ => exact hVer
  round_flip_bound := fun stmt r pref msg hPrefLen hDoomed L hNd hL => by
    have hr0 : r.1 = 0 := by have := r.isLt; omega
    cases pref with
    | cons _ _ => rw [hr0] at hPrefLen; cases hPrefLen
    | nil =>
      have hNoWit : ¬ ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth,
          BlindVcWitnessValid stmt wit := hDoomed
      let p : Nat → Fin 3 → Bool := fun idx e =>
        if hIdx : idx < k then
          verifyCollisionFreeCommittedBlindVcRep H prgExpand stmt idx (Vec.get msg.allRound1 ⟨idx, hIdx⟩)
            (Vec.get msg.openTable ⟨idx, hIdx⟩).get e
        else true
      let verFn : Fin (3 ^ k) → Bool :=
        fun c => (blindVcParallelIop H prgExpand k).verify stmt [(msg, c.1)]
      have hSub : ∀ ch ∈ L, ch ∈ finFilterList (3 ^ k) verFn :=
        fun ch hch => finFilterList_complete (3 ^ k) verFn ch (Decidable.of_not_not (hL ch hch))
      have hLenLe : L.length ≤ qsum (3 ^ k) (fun c => if verFn c = true then 1 else 0) :=
        Nat.le_trans (nodup_length_le_of_subset hNd hSub)
          (Nat.le_of_eq (finFilterList_length (3 ^ k) verFn))
      have hEqRange : ∀ c : Fin (3 ^ k),
          verFn c =
          (List.range k).all
            (fun idx => if hM : 0 < 3 then p idx ⟨(c.1 / 3 ^ idx) % 3, Nat.mod_lt _ hM⟩ else false) :=
        fun _ => rfl
      have hEach : ∀ idx < k, qsum 3 (fun e => if p idx e = true then 1 else 0) ≤ 2 := by
        intro idx hlt
        have hP : ∀ e : Fin 3, p idx e =
            verifyCollisionFreeCommittedBlindVcRep H prgExpand stmt idx (Vec.get msg.allRound1 ⟨idx, hlt⟩)
              (Vec.get msg.openTable ⟨idx, hlt⟩).get e := fun _ => dite_true hlt _ _
        rw [qsum_congr (fun e => by rw [hP e])]
        exact blindVc_rep_pigeonhole_le_two hHLen hNoWit idx
          (Vec.get msg.allRound1 ⟨idx, hlt⟩) ((Vec.get msg.openTable ⟨idx, hlt⟩).get)
      refine Nat.le_trans hLenLe ?_
      rw [qsum_congr (fun c => by rw [hEqRange c])]
      exact product_bad_count_le_pow 3 2 k p hEach

/-- **Interactive `438`-Repetition State-Restoration Soundness (`blindVc_quantum128_interactive_rbr_bound`)**. -/
theorem blindVc_quantum128_interactive_rbr_bound
    {H : List UInt8 → List UInt8} (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement)
    (hNotInLang : ¬ (blindVcParallelIop H prgExpand 438).inLang stmt)
    (sched : List (Fin 1))
    (tree : SrScheduleTree (blindVcParallelIop H prgExpand 438) sched) :
    2 ^ 438 * 2 ^ 256 < 3 ^ 438 ∧
    RatBound.le (srTreeAcceptProb (blindVcParallelIop H prgExpand 438) tree stmt)
      (srScheduleErrorSum (blindVcParallelRbr hHLen prgExpand 438) sched) :=
  ⟨by decide,
   rbr_implies_state_restoration_soundness (blindVcParallelRbr hHLen prgExpand 438) stmt hNotInLang sched tree⟩

/-! ## §2. Multi-Round QROM Fiat-Shamir `QromRbrRound` (`u64 % 3` Squeeze, `Q ≤ 2^60 => < 2^-128`) -/

def blindVcQuot64 : Nat := 6148914691236517205
def blindVcBadWord64 : Nat := 12297829382473034411

theorem word64_mod3_bad_count_le (p : Fin 3 → Bool) (hNotAll : fin3AllTrue p = false) :
    qsum (2 ^ 64) (fun u => if p ⟨u.1 % 3, Nat.mod_lt _ (by decide)⟩ = true then 1 else 0) ≤
      blindVcBadWord64 := by
  have hDecomp : 2 ^ 64 = blindVcQuot64 * 3 + 1 := by decide
  rw [qsum_cast hDecomp, qsum_add_split_local (blindVcQuot64 * 3) 1, qsum_mul_factor blindVcQuot64 3]
  have hBlock : ∀ q : Fin blindVcQuot64,
      qsum 3 (fun r => if p ⟨(q.1 * 3 + r.1) % 3, Nat.mod_lt _ (by decide)⟩ = true then 1 else 0) ≤ 2 := by
    intro q
    have hCong : ∀ r : Fin 3,
        (if p ⟨(q.1 * 3 + r.1) % 3, Nat.mod_lt _ (by decide)⟩ = true then 1 else 0) =
        (if p r = true then 1 else 0) := by
      intro r; have hr := r.isLt
      have hFin : (⟨(q.1 * 3 + r.1) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = r := by
        apply Fin.ext; dsimp only; omega
      rw [hFin]
    rw [qsum_congr hCong]; exact fin3_not_all_count_le_two p hNotAll
  have hBlocksLe :
      qsum blindVcQuot64 (fun q => qsum 3 (fun r =>
        if p ⟨(q.1 * 3 + r.1) % 3, Nat.mod_lt _ (by decide)⟩ = true then 1 else 0)) ≤
      blindVcQuot64 * 2 := by
    refine Nat.le_trans (qsum_le_qsum hBlock) ?_; rw [qsum_const]; exact Nat.le_refl _
  have hTailLe :
      qsum 1 (fun y =>
        if p ⟨(blindVcQuot64 * 3 + y.1) % 3, Nat.mod_lt _ (by decide)⟩ = true then 1 else 0) ≤ 1 := by
    simp only [qsum_succ, qsum_zero, Nat.add_zero]
    cases p ⟨(blindVcQuot64 * 3 + 0) % 3, Nat.mod_lt _ (by decide)⟩ <;> decide
  have hSum := Nat.add_le_add hBlocksLe hTailLe
  unfold blindVcBadWord64 blindVcQuot64 at hSum ⊢; omega

def squeeze64Mod3At {k : Nat} (bv : BitVec (64 * k)) (idx : Nat) : Fin 3 :=
  ⟨((bv.toNat / ((2 ^ 64) ^ idx)) % (2 ^ 64)) % 3, Nat.mod_lt _ (by decide)⟩

def blindVcFsLiveAfter {cardX k : Nat}
    (H_hash : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : Fin cardX → BlindVcParallelMsg k)
    (O' : Fin cardX → BitVec (64 * k)) (x : Fin cardX) : Bool :=
  (List.range k).all (fun idx =>
    if hIdx : idx < k then
      let fi : Fin k := ⟨idx, hIdx⟩
      let e := squeeze64Mod3At (O' x) idx
      verifyCollisionFreeCommittedBlindVcRep H_hash prgExpand (stmtAt x) idx
        (Vec.get (msgAt x).allRound1 fi) (Vec.get (msgAt x).openTable fi).get e
    else true)

/-- The unfiltered verifier event on the supplied table. This is separate from the
collision-filtered event bounded by the statistical QROM theorem. -/
def blindVcFsUnfilteredLiveAfter {cardX k : Nat}
    (H_hash : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : Fin cardX → BlindVcParallelMsg k)
    (O' : Fin cardX → BitVec (64 * k)) (x : Fin cardX) : Bool :=
  (List.range k).all (fun idx =>
    if hIdx : idx < k then
      let fi : Fin k := ⟨idx, hIdx⟩
      let e := squeeze64Mod3At (O' x) idx
      verifyCommittedBlindVcRep H_hash prgExpand (stmtAt x) idx
        (Vec.get (msgAt x).allRound1 fi) e ((Vec.get (msgAt x).openTable fi).get e)
    else true)

/-- A finite bad event in the actual supplied opening table, independent of any
unrelated collisions elsewhere in the hash function's domain. -/
def blindVcTableConflict {k : Nat} (H : List UInt8 → List UInt8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) : Bool :=
  (List.range k).any (fun idx =>
    if hIdx : idx < k then
      let cand := (Vec.get msg.openTable ⟨idx, hIdx⟩).get
      decide (VcRewoundCommitConflict H stmt.presNonce idx (cand 0) (cand 1) (cand 2))
    else false)

theorem blindVcTableConflict_eq {k : Nat} (H : List UInt8 → List UInt8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) :
    blindVcTableConflict H stmt msg =
      (List.range k).any (fun idx =>
        if hIdx : idx < k then
          let cand := (Vec.get msg.openTable ⟨idx, hIdx⟩).get
          decide (VcRewoundCommitConflict H stmt.presNonce idx (cand 0) (cand 1) (cand 2))
        else false) := by rfl

theorem blindVcTableConflict_extract {k : Nat}
    {H : List UInt8 → List UInt8} {stmt : BlindVcPublicStatement}
    {msg : BlindVcParallelMsg k} (h : blindVcTableConflict H stmt msg = true) :
    ∃ idx : Fin k, let cand := (Vec.get msg.openTable idx).get
      VcRewoundCommitConflict H stmt.presNonce idx.val (cand 0) (cand 1) (cand 2) := by
  obtain ⟨idx, hMem, hHit⟩ := List.any_eq_true.mp h
  have hlt : idx < k := List.mem_range.mp hMem
  rw [dite_true hlt] at hHit
  exact ⟨⟨idx, hlt⟩, of_decide_eq_true hHit⟩

/-- The total acceptance event decomposes before assigning any numerical bound.
A separate computational bound for `blindVcTableConflict` is required to turn the
filtered QROM mass estimate into a total soundness estimate. -/
theorem blindVc_fs_acceptance_decomposition {cardX k : Nat}
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : Fin cardX → BlindVcParallelMsg k)
    (O : Fin cardX → BitVec (64 * k)) (x : Fin cardX)
    (hAccept : blindVcFsUnfilteredLiveAfter H prgExpand stmtAt msgAt O x = true) :
    blindVcTableConflict H (stmtAt x) (msgAt x) = true ∨
    blindVcFsLiveAfter H prgExpand stmtAt msgAt O x = true := by
  cases hc : blindVcTableConflict H (stmtAt x) (msgAt x) with
  | true => exact Or.inl rfl
  | false =>
    right
    apply List.all_eq_true.mpr
    intro idx hMem
    have hlt : idx < k := List.mem_range.mp hMem
    have hRaw := List.all_eq_true.mp hAccept idx hMem
    have hClean := List.any_eq_false.mp hc idx hMem
    rw [dite_true hlt] at hRaw hClean ⊢
    simp only [verifyCollisionFreeCommittedBlindVcRep, hClean, Bool.not_false,
      Bool.true_and]
    exact hRaw

/-- Constructive `QromRbrRound` instantiation for `k`-repetition `BlindVC` Fiat-Shamir squeezing. -/
def blindVcQromFsRound
    {cardX : Nat} {H_hash : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H_hash m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (k : Nat) (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : (x : Fin cardX) → BlindVcParallelMsg k)
    (isDoomedBool : Fin cardX → Bool)
    (hDoomedSound : ∀ x : Fin cardX, isDoomedBool x = true →
      ¬ (blindVcParallelIop H_hash prgExpand k).inLang (stmtAt x))
    (O : Fin cardX → BitVec (64 * k)) : QromRbrRound cardX (64 * k) O where
  proj := id
  isDoomedAt := fun _ x => isDoomedBool x
  isLiveAfter := blindVcFsLiveAfter H_hash prgExpand stmtAt msgAt
  badCard := blindVcBadWord64 ^ k
  doomed_local := fun _ _ => rfl
  flip_bound := fun x hD => by
    have hNotIn := hDoomedSound x hD
    have hNoWit : ¬ ∃ wit : BlindVcSecretWitness (stmtAt x).schema.arity (stmtAt x).treeDepth,
        BlindVcWitnessValid (stmtAt x) wit := hNotIn
    let p : Nat → Fin (2 ^ 64) → Bool := fun idx u =>
      if hIdx : idx < k then
        let fi : Fin k := ⟨idx, hIdx⟩
        let e : Fin 3 := ⟨u.1 % 3, Nat.mod_lt _ (by decide)⟩
        verifyCollisionFreeCommittedBlindVcRep H_hash prgExpand (stmtAt x) idx
          (Vec.get (msgAt x).allRound1 fi) (Vec.get (msgAt x).openTable fi).get e
      else true
    have hEach : ∀ idx < k, qsum (2 ^ 64) (fun u => if p idx u = true then 1 else 0) ≤
        blindVcBadWord64 := by
      intro idx hlt
      let fi : Fin k := ⟨idx, hlt⟩
      let q3 : Fin 3 → Bool := fun e =>
        verifyCollisionFreeCommittedBlindVcRep H_hash prgExpand (stmtAt x) idx
          (Vec.get (msgAt x).allRound1 fi) (Vec.get (msgAt x).openTable fi).get e
      have hNotAll3 : fin3AllTrue q3 = false := by
        unfold fin3AllTrue
        cases hAll : (q3 0 && q3 1 && q3 2) with
        | false => rfl
        | true =>
          have h3 : qsum 3 (fun e => if q3 e = true then 1 else 0) = 3 := by
            simp only [Bool.and_eq_true] at hAll; rcases hAll with ⟨⟨h0, h1⟩, h2⟩
            simp only [qsum_succ, qsum_zero, Nat.add_zero]
            change (if q3 0 = true then 1 else 0) +
              ((if q3 1 = true then 1 else 0) + (if q3 2 = true then 1 else 0)) = 3
            rw [h0, h1, h2]; decide
          have hLe2 := blindVc_rep_pigeonhole_le_two (prgExpand := prgExpand) hHLen hNoWit idx
            (Vec.get (msgAt x).allRound1 fi) ((Vec.get (msgAt x).openTable fi).get)
          change qsum 3 (fun e => if q3 e = true then 1 else 0) ≤ 2 at hLe2; omega
      have hCong : ∀ u : Fin (2 ^ 64),
          (if p idx u = true then 1 else 0) =
          (if q3 ⟨u.1 % 3, Nat.mod_lt _ (by decide)⟩ = true then 1 else 0) := by
        intro u
        have hpu : p idx u = q3 ⟨u.1 % 3, Nat.mod_lt _ (by decide)⟩ := dite_true hlt _ _
        rw [hpu]
      rw [qsum_congr hCong]; exact word64_mod3_bad_count_le q3 hNotAll3
    have hPowEq : 2 ^ (64 * k) = (2 ^ 64) ^ k := Nat.pow_mul 2 64 k
    rw [qsum_cast hPowEq]
    refine Nat.le_trans ?_ (product_bad_count_le_pow (2 ^ 64) blindVcBadWord64 k p hEach)
    apply qsum_le_qsum; intro ch
    have hChLt : ch.1 < 2 ^ (64 * k) := by rw [hPowEq]; exact ch.isLt
    let chBv : BitVec (64 * k) := BitVec.ofFin ⟨ch.1, hChLt⟩
    have hReprog : (reprogramOracle O x chBv x).toNat = ch.1 := by
      rw [reprogramOracle_self]; rfl
    have hAllEq :
        blindVcFsLiveAfter H_hash prgExpand stmtAt msgAt (reprogramOracle O x chBv) x =
        (List.range k).all (fun idx =>
          if hM : 0 < 2 ^ 64 then p idx ⟨(ch.1 / (2 ^ 64) ^ idx) % 2 ^ 64, Nat.mod_lt _ hM⟩
          else false) := by
      unfold blindVcFsLiveAfter
      congr 1; funext idx
      rw [dite_true (Nat.two_pow_pos 64)]
      have hFinEq : squeeze64Mod3At (reprogramOracle O x chBv x) idx =
          ⟨((ch.1 / (2 ^ 64) ^ idx) % 2 ^ 64) % 3, Nat.mod_lt _ (by decide)⟩ := by
        apply Fin.ext; dsimp only [squeeze64Mod3At]; rw [hReprog]
      dsimp only [p]; rw [hFinEq]
    change (if blindVcFsLiveAfter H_hash prgExpand stmtAt msgAt (reprogramOracle O x chBv) x = true
      then 1 else 0) ≤ _
    rw [hAllEq]; exact Nat.le_refl _

/-- Parametric `k`-repetition QROM Fiat-Shamir round bound (symbolic in `k`, zero big-int WHNF). -/
theorem blindVc_qrom_fs_round_bound
    {cardX cardAnc Q : Nat} (k : Nat)
    (A : QuantumAdv cardX (64 * k) cardAnc Q)
    {H_hash : List UInt8 → List UInt8} (hHLen : ∀ m, (H_hash m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : (x : Fin cardX) → BlindVcParallelMsg k)
    (isDoomedBool : Fin cardX → Bool)
    (hDoomedSound : ∀ x : Fin cardX, isDoomedBool x = true →
      ¬ (blindVcParallelIop H_hash prgExpand k).inLang (stmtAt x)) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum (64 * k) cardX
         (fun O => qromOrdinaryFlipMass A O id (fun _ x => isDoomedBool x)
           (blindVcFsLiveAfter H_hash prgExpand stmtAt msgAt)),
       (2 ^ (64 * k)) ^ cardX * norm,
       Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _))
         (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * blindVcBadWord64 ^ k, 2 ^ (64 * k), Nat.two_pow_pos _⟩ :=
  qrom_uniform_oracle_round_bound A
    (blindVcQromFsRound hHLen prgExpand k stmtAt msgAt isDoomedBool hDoomedSound)
    id (fun _ x => isDoomedBool x)
    (blindVcFsLiveAfter H_hash prgExpand stmtAt msgAt)
    (blindVcBadWord64 ^ k) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- **Flagship §2 Theorem — `438`-Repetition QROM Fiat-Shamir Soundness (`blindVc_quantum128_qrom_fs_soundness`)**:
    Bounds the defined collision-filtered doomed-to-live query mass by `(2 * Q + 1)^2 * blindVcBadWord64^438 / 2^(64 * 438)`,
    strictly `< 2^-128` for all `Q ≤ 2^60` quantum random-oracle queries. -/
theorem blindVc_quantum128_qrom_fs_soundness
    {cardX cardAnc Q : Nat} (hQ : Q ≤ 2 ^ 60)
    (A : QuantumAdv cardX (64 * 438) cardAnc Q)
    {H_hash : List UInt8 → List UInt8} (hHLen : ∀ m, (H_hash m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : (x : Fin cardX) → BlindVcParallelMsg 438)
    (isDoomedBool : Fin cardX → Bool)
    (hDoomedSound : ∀ x : Fin cardX, isDoomedBool x = true →
      ¬ (blindVcParallelIop H_hash prgExpand 438).inLang (stmtAt x)) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum (64 * 438) cardX
         (fun O => qromOrdinaryFlipMass A O id (fun _ x => isDoomedBool x)
           (blindVcFsLiveAfter H_hash prgExpand stmtAt msgAt)),
       (2 ^ (64 * 438)) ^ cardX * norm,
       Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _))
         (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * blindVcBadWord64 ^ 438, 2 ^ (64 * 438), Nat.two_pow_pos _⟩ ∧
    (2 * Q + 1) ^ 2 * blindVcBadWord64 ^ 438 * 2 ^ 128 < (2 ^ 64) ^ 438 := by
  refine ⟨blindVc_qrom_fs_round_bound 438 A hHLen prgExpand stmtAt msgAt isDoomedBool hDoomedSound, ?_⟩
  have hStepRatio : blindVcBadWord64 * 3071 ≤ 2 ^ 64 * 2048 := by decide
  have hPowRatio : (blindVcBadWord64 * 3071) ^ 438 ≤ (2 ^ 64 * 2048) ^ 438 :=
    Nat.pow_le_pow_left hStepRatio 438
  rw [Nat.mul_pow, Nat.mul_pow] at hPowRatio
  have hQMono : (2 * Q + 1) ^ 2 ≤ (2 * 2 ^ 60 + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hMargin : (2 * 2 ^ 60 + 1) ^ 2 * 2048 ^ 438 * 2 ^ 128 < 3071 ^ 438 := by decide
  have hQMargin : (2 * Q + 1) ^ 2 * 2048 ^ 438 * 2 ^ 128 < 3071 ^ 438 :=
    Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_right (2 ^ 128) (Nat.mul_le_mul_right (2048 ^ 438) hQMono)) hMargin
  apply nat_lt_of_mul_lt_mul_right (c := 3071 ^ 438)
  have hLhsEq :
      (2 * Q + 1) ^ 2 * blindVcBadWord64 ^ 438 * 2 ^ 128 * 3071 ^ 438 =
      ((2 * Q + 1) ^ 2 * 2 ^ 128) * (blindVcBadWord64 ^ 438 * 3071 ^ 438) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hMidLe :
      ((2 * Q + 1) ^ 2 * 2 ^ 128) * (blindVcBadWord64 ^ 438 * 3071 ^ 438) ≤
      ((2 * Q + 1) ^ 2 * 2048 ^ 438 * 2 ^ 128) * (2 ^ 64) ^ 438 := by
    have h1 := Nat.mul_le_mul_left ((2 * Q + 1) ^ 2 * 2 ^ 128) hPowRatio
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h1
  have hStrict :
      ((2 * Q + 1) ^ 2 * 2048 ^ 438 * 2 ^ 128) * (2 ^ 64) ^ 438 <
      3071 ^ 438 * (2 ^ 64) ^ 438 :=
    Nat.mul_lt_mul_of_pos_right hQMargin (Nat.pow_pos (Nat.two_pow_pos 64))
  rw [hLhsEq, Nat.mul_comm ((2 ^ 64) ^ 438) (3071 ^ 438)]
  exact Nat.lt_of_le_of_lt hMidLe hStrict

/-! ## §3. Merkle Path Bridge & Issuer `ML-DSA` Root-Attestation Unforgeability -/

def vcBoolStepsIdx : List (Bool × Lane6) → Nat
  | [] => 0
  | (b, _) :: rest => (if b then 1 else 0) + 2 * vcBoolStepsIdx rest

theorem evalVcMerklePathBool_eq_merkleRootFromPath (epoch : UInt64) :
    ∀ (layer : Nat) (cur : Lane6) (steps : List (Bool × Lane6)),
      evalVcMerklePathBool epoch layer cur steps =
        merkleRootFromPath (fun lvl _ l r => vcMerkleHashPair l r epoch lvl)
          layer (vcBoolStepsIdx steps) cur (steps.map Prod.snd)
  | layer, cur, [] => by
    rw [evalVcMerklePathBool_nil]
    exact (merkleRootFromPath_nil _ layer 0 cur).symm
  | layer, cur, (false, sib) :: rest => by
    have hMod : (0 + 2 * vcBoolStepsIdx rest) % 2 = 0 := by omega
    have hDiv : (0 + 2 * vcBoolStepsIdx rest) / 2 = vcBoolStepsIdx rest := by omega
    rw [evalVcMerklePathBool_cons_false]
    show _ = merkleRootFromPath _ layer (0 + 2 * vcBoolStepsIdx rest) cur (sib :: rest.map Prod.snd)
    rw [merkleRootFromPath_cons, ite_true hMod, hDiv]
    exact evalVcMerklePathBool_eq_merkleRootFromPath epoch (layer + 1) _ rest
  | layer, cur, (true, sib) :: rest => by
    have hMod : (1 + 2 * vcBoolStepsIdx rest) % 2 ≠ 0 := by omega
    have hDiv : (1 + 2 * vcBoolStepsIdx rest) / 2 = vcBoolStepsIdx rest := by omega
    rw [evalVcMerklePathBool_cons_true]
    show _ = merkleRootFromPath _ layer (1 + 2 * vcBoolStepsIdx rest) cur (sib :: rest.map Prod.snd)
    rw [merkleRootFromPath_cons, ite_false hMod, hDiv]
    exact evalVcMerklePathBool_eq_merkleRootFromPath epoch (layer + 1) _ rest

inductive VcMerkleTree : Nat → Type where
  | leaf (val : Lane6) : VcMerkleTree 0
  | branch {d : Nat} (left right : VcMerkleTree d) : VcMerkleTree (d + 1)

def vcMerkleTreeRoot (epoch : UInt64) : {d : Nat} → Nat → VcMerkleTree d → Lane6
  | 0, _, .leaf v => v
  | d + 1, layer, .branch l r =>
    vcMerkleHashPair (vcMerkleTreeRoot epoch layer l) (vcMerkleTreeRoot epoch layer r) epoch (layer + d)

def vcMerkleTreeLeaves : {d : Nat} → VcMerkleTree d → List Lane6
  | 0, .leaf v => [v]
  | _ + 1, .branch l r => vcMerkleTreeLeaves l ++ vcMerkleTreeLeaves r

private def listSnocSplit {α : Type} : (x : α) → (xs : List α) →
    { p : List α × α // x :: xs = p.1 ++ [p.2] ∧ p.1.length = xs.length }
  | x, [] => ⟨([], x), rfl, rfl⟩
  | x, y :: ys =>
    let ⟨(ini, lst), hEq, hLen⟩ := listSnocSplit y ys
    ⟨(x :: ini, lst), by simp [hEq], by simp [hLen]⟩

private theorem evalVcMerklePathBool_append_singleton (epoch : UInt64) :
    ∀ (steps : List (Bool × Lane6)) (layer : Nat) (cur : Lane6) (b : Bool) (sib : Lane6),
      evalVcMerklePathBool epoch layer cur (steps ++ [(b, sib)]) =
        (if b then vcMerkleHashPair sib (evalVcMerklePathBool epoch layer cur steps) epoch (layer + steps.length)
         else vcMerkleHashPair (evalVcMerklePathBool epoch layer cur steps) sib epoch (layer + steps.length))
  | [], _, _, false, _ => by
    simp only [List.nil_append, evalVcMerklePathBool_cons_false, evalVcMerklePathBool_nil,
      Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.add_zero]
  | [], _, _, true, _ => by
    simp only [List.nil_append, evalVcMerklePathBool_cons_true, evalVcMerklePathBool_nil,
      ↓reduceIte, List.length_nil, Nat.add_zero]
  | (b0, _) :: rest, layer, _, b, sib => by
    cases b0 <;>
      simp only [List.cons_append, evalVcMerklePathBool_cons_false, evalVcMerklePathBool_cons_true,
        List.length_cons] <;>
      rw [evalVcMerklePathBool_append_singleton epoch rest (layer + 1) _ b sib] <;>
      rw [show layer + 1 + rest.length = layer + (rest.length + 1) by omega]

/-- **Merkle Accumulator Membership or Reachable Sponge Collision (`vcMerkleTree_opening_sound`)**. -/
theorem vcMerkleTree_opening_sound (epoch : UInt64) :
    ∀ {d : Nat} (tree : VcMerkleTree d) (layer : Nat) (leaf : Lane6) (steps : List (Bool × Lane6)),
      steps.length = d → evalVcMerklePathBool epoch layer leaf steps = vcMerkleTreeRoot epoch layer tree →
      leaf ∈ vcMerkleTreeLeaves tree ∨
      ∃ (c₁ c₂ : Lane6 × Lane6 × Lane6) (r : Fin 3),
        Poseidon2Perm12Sponge6Collision (spongeTrace204 c₁ r) (spongeTrace204 c₂ r)
  | 0, .leaf _, _, _, [], _, hEq =>
    Or.inl (by
      rw [evalVcMerklePathBool_nil] at hEq; dsimp only [vcMerkleTreeRoot] at hEq
      rw [hEq]; exact .head [])
  | 0, .leaf _, _, _, _ :: _, hLen, _ => by cases hLen
  | _ + 1, .branch _ _, _, _, [], hLen, _ => by cases hLen
  | d + 1, .branch lTree rTree, layer, leaf, s0 :: sRest, hLen, hEq => by
    obtain ⟨⟨ini, bTop, sibTop⟩, hSplit, hIniLen⟩ := listSnocSplit s0 sRest
    dsimp only at hSplit hIniLen
    have hd : ini.length = d := by simp only [List.length_cons] at hLen; omega
    rw [hSplit, evalVcMerklePathBool_append_singleton, hd] at hEq
    simp only [vcMerkleTreeRoot] at hEq
    let subRoot := evalVcMerklePathBool epoch layer leaf ini
    let lRoot := vcMerkleTreeRoot epoch layer lTree
    let rRoot := vcMerkleTreeRoot epoch layer rTree
    cases bTop with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hEq
      if hChildren : subRoot = lRoot ∧ sibTop = rRoot then
        rcases vcMerkleTree_opening_sound epoch lTree layer leaf ini hd hChildren.1 with hMem | hColl
        · exact Or.inl (List.mem_append_left _ hMem)
        · exact Or.inr hColl
      else
        have hChunksNe : vcMerkleChunks subRoot sibTop epoch (layer + d) ≠
            vcMerkleChunks lRoot rRoot epoch (layer + d) :=
          fun hc => hChildren (vcMerkleChunks_children_inj hc)
        rw [vcMerkleHashPair_eq, vcMerkleHashPair_eq] at hEq
        obtain ⟨r, hCol⟩ := absorbRate6Sponge3_reachable_collision204 hChunksNe hEq
        exact Or.inr ⟨_, _, r, hCol⟩
    | true =>
      simp only [↓reduceIte] at hEq
      if hChildren : sibTop = lRoot ∧ subRoot = rRoot then
        rcases vcMerkleTree_opening_sound epoch rTree layer leaf ini hd hChildren.2 with hMem | hColl
        · exact Or.inl (List.mem_append_right _ hMem)
        · exact Or.inr hColl
      else
        have hChunksNe : vcMerkleChunks sibTop subRoot epoch (layer + d) ≠
            vcMerkleChunks lRoot rRoot epoch (layer + d) :=
          fun hc => hChildren (vcMerkleChunks_children_inj hc)
        rw [vcMerkleHashPair_eq, vcMerkleHashPair_eq] at hEq
        obtain ⟨r, hCol⟩ := absorbRate6Sponge3_reachable_collision204 hChunksNe hEq
        exact Or.inr ⟨_, _, r, hCol⟩

/-! ### Issuer root attestation (`IssuerRootAttestation` of `blind_vc.rs`)

The issuer signs `signing_message(issuer_pk_digest, issuer_epoch, accumulator_root, root_tag)`
under the context `SIGNING_CONTEXT` with FIPS 204 ML-DSA. `ml_dsa_verify` does not hash the
message into the challenge directly: it first forms the 64-byte message representative
`μ = SHAKE256(SHAKE256(pk, 64) ‖ 0x00 ‖ |ctx| ‖ ctx ‖ M, 64)` (`compute_fips204_mu`). -/

/-- ASCII `QSAG.VC.ROOT_ATTEST.V1`: the prefix of `IssuerRootAttestation::signing_message`. -/
def issuerRootAttestationTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x56, 0x43, 0x2E, 0x52, 0x4F, 0x4F, 0x54, 0x5F,
   0x41, 0x54, 0x54, 0x45, 0x53, 0x54, 0x2E, 0x56, 0x31]

/-- ASCII `QSAG.VC.ROOT_ATTEST.CTX.V1`: `IssuerRootAttestation::SIGNING_CONTEXT`. -/
def issuerRootAttestationCtx : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x56, 0x43, 0x2E, 0x52, 0x4F, 0x4F, 0x54, 0x5F,
   0x41, 0x54, 0x54, 0x45, 0x53, 0x54, 0x2E, 0x43, 0x54, 0x58, 0x2E, 0x56, 0x31]

theorem issuerRootAttestationCtx_length : issuerRootAttestationCtx.length = 26 := by rfl

/-- The 142-byte message of `IssuerRootAttestation::signing_message`: 22-byte tag, 32-byte
issuer key digest, 8-byte little-endian epoch, six 8-byte little-endian root limbs, 32-byte
root tag. -/
def encodeIssuerRootAttestationMsg (issuerPkDigest : Vec UInt8 32) (epoch : UInt64)
    (accRoot : Lane6) (issuerRootTag : Vec UInt8 32) : List UInt8 :=
  issuerRootAttestationTag ++
  (issuerPkDigest.toList ++ (encodeNatLeBytes 8 epoch.toNat ++
  (encodeGoldilocksVecLe [accRoot.x0, accRoot.x1, accRoot.x2, accRoot.x3, accRoot.x4, accRoot.x5] ++
  issuerRootTag.toList)))

theorem encodeIssuerRootAttestationMsg_length (issuerPkDigest : Vec UInt8 32) (epoch : UInt64)
    (accRoot : Lane6) (issuerRootTag : Vec UInt8 32) :
    (encodeIssuerRootAttestationMsg issuerPkDigest epoch accRoot issuerRootTag).length = 142 := by
  unfold encodeIssuerRootAttestationMsg issuerRootAttestationTag
  simp only [List.length_append, List.length_cons, List.length_nil, Vec.toList_length,
    encodeNatLeBytes_length, encodeGoldilocksVecLe_length]

/-- The message determines all four signed fields. -/
theorem encodeIssuerRootAttestationMsg_injective
    {dig₁ dig₂ tag₁ tag₂ : Vec UInt8 32} {ep₁ ep₂ : UInt64} {root₁ root₂ : Lane6}
    (hEq : encodeIssuerRootAttestationMsg dig₁ ep₁ root₁ tag₁ =
           encodeIssuerRootAttestationMsg dig₂ ep₂ root₂ tag₂) :
    dig₁ = dig₂ ∧ ep₁ = ep₂ ∧ root₁ = root₂ ∧ tag₁ = tag₂ := by
  unfold encodeIssuerRootAttestationMsg at hEq
  obtain ⟨_, hRest1⟩ := List.append_inj hEq rfl
  have hDigLen : dig₁.toList.length = dig₂.toList.length := by
    rw [Vec.toList_length, Vec.toList_length]
  obtain ⟨hDigBytes, hRest2⟩ := List.append_inj hRest1 hDigLen
  have hEpLen : (encodeNatLeBytes 8 ep₁.toNat).length = (encodeNatLeBytes 8 ep₂.toNat).length := by
    rw [encodeNatLeBytes_length, encodeNatLeBytes_length]
  obtain ⟨hEpBytes, hRest3⟩ := List.append_inj hRest2 hEpLen
  have hRootLen :
      (encodeGoldilocksVecLe [root₁.x0, root₁.x1, root₁.x2, root₁.x3, root₁.x4, root₁.x5]).length =
      (encodeGoldilocksVecLe [root₂.x0, root₂.x1, root₂.x2, root₂.x3, root₂.x4, root₂.x5]).length := by
    rw [encodeGoldilocksVecLe_length, encodeGoldilocksVecLe_length]; rfl
  obtain ⟨hRootBytes, hTagBytes⟩ := List.append_inj hRest3 hRootLen
  have hEp1Lt : ep₁.toNat < 256 ^ 8 := by
    have h := ep₁.toNat_lt_size; change ep₁.toNat < 18446744073709551616 at h; omega
  have hEp2Lt : ep₂.toNat < 256 ^ 8 := by
    have h := ep₂.toNat_lt_size; change ep₂.toNat < 18446744073709551616 at h; omega
  have hEpNat : ep₁.toNat = ep₂.toNat := by
    have hd := congrArg decodeNatLeBytes hEpBytes
    rwa [decodeNatLeBytes_encodeNatLeBytes 8 ep₁.toNat hEp1Lt,
         decodeNatLeBytes_encodeNatLeBytes 8 ep₂.toNat hEp2Lt] at hd
  have hLimbs := encodeGoldilocksVecLe_injective hRootBytes
  simp only [List.cons.injEq] at hLimbs
  rcases hLimbs with ⟨e0, e1, e2, e3, e4, e5, _⟩
  exact ⟨Vec.toList_injective hDigBytes, UInt64.toNat_inj.mp hEpNat,
    Lane6.ext e0 e1 e2 e3 e4 e5, Vec.toList_injective hTagBytes⟩

/-- FIPS 204 message representative
`μ = SHAKE256(SHAKE256(pk, 64) ‖ 0x00 ‖ |ctx| ‖ ctx ‖ M, 64)` (`compute_fips204_mu`; the same
expression appears inside `mldsaVerifyBytes204`). -/
def fips204MessageRepresentative (pk ctx msg : List UInt8) : List UInt8 :=
  shake256Xof 64 (shake256Xof 64 pk ++ [0, UInt8.ofNat ctx.length] ++ ctx ++ msg)

theorem fips204MessageRepresentative_length (pk ctx msg : List UInt8) :
    (fips204MessageRepresentative pk ctx msg).length = 64 :=
  shake256Xof_length 64 _

/-- The attested fields of one issuer root attestation. -/
structure IssuerRootAttestationFields where
  issuerPkDigest : Vec UInt8 32
  issuerEpoch : UInt64
  accumulatorRoot : Lane6
  issuerRootTag : Vec UInt8 32
  deriving DecidableEq

def IssuerRootAttestationFields.message (f : IssuerRootAttestationFields) : List UInt8 :=
  encodeIssuerRootAttestationMsg f.issuerPkDigest f.issuerEpoch f.accumulatorRoot f.issuerRootTag

theorem IssuerRootAttestationFields.message_injective {f g : IssuerRootAttestationFields}
    (h : f.message = g.message) : f = g := by
  obtain ⟨h1, h2, h3, h4⟩ := encodeIssuerRootAttestationMsg_injective h
  cases f; cases g; cases h1; cases h2; cases h3; cases h4; rfl

/-- Root-attestation check on the algebraic ML-DSA core: the challenge hash is taken over the
message representative of the attestation message under the issuer key bytes `issuerPk`, as in
`IssuerRootAttestation::verify`. -/
def verifyIssuerRootAttestation
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8) (sampleInBall : List UInt8 → Poly256)
    (issuerA : PolyMat4) (issuerT1Scaled : PolyVec4) (issuerPk : List UInt8)
    (f : IssuerRootAttestationFields) (rootSig : ThresholdSignSig) : Bool :=
  mldsaVerify chalHash sampleInBall issuerA issuerT1Scaled
    (fips204MessageRepresentative issuerPk issuerRootAttestationCtx f.message)
    rootSig.cTilde rootSig.z rootSig.h

/-- The same check on wire bytes: the standalone ML-DSA-44 verifier applied to the issuer key,
the attestation message, the attestation context and the signature bytes. -/
@[expose] def verifyIssuerRootAttestationBytes (byteBudget : Nat) (issuerPk : List UInt8)
    (f : IssuerRootAttestationFields) (sig : List UInt8) : Bool :=
  mldsaVerifyBytes204 byteBudget issuerPk f.message issuerRootAttestationCtx sig

/-- An attestation accepted on wire bytes is accepted by the algebraic core, with the decoded
key and signature, at the FIPS 204 message representative. -/
theorem verifyIssuerRootAttestationBytes_accepts_core {byteBudget : Nat} {issuerPk : List UInt8}
    {f : IssuerRootAttestationFields} {sig : List UInt8}
    (h : verifyIssuerRootAttestationBytes byteBudget issuerPk f sig = true) :
    ∃ (A : PolyMat4) (t1Scaled : PolyVec4) (c : Poly256) (decoded : DecodedSignature204),
      decodeSignature204 sig = some decoded ∧
      verifyIssuerRootAttestation mldsa44ChallengeHash (fun _ => c) A t1Scaled issuerPk f
        ⟨decoded.challenge, decoded.z, decoded.hints, 0⟩ = true := by
  obtain ⟨A, t1Scaled, c, decoded, hDec, hCore⟩ := mldsaVerifyBytes204_accepts_core h
  exact ⟨A, t1Scaled, c, decoded, hDec, hCore⟩

/-- A challenge hash that separates message representatives rejects, at the FIPS 204 message
representative, every signature that verifies with the raw message in its place. The raw
message is never a message representative of the attestation: it has 142 bytes, not 64. -/
theorem verifyIssuerRootAttestation_rejects_raw_message_signature
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8} {sampleInBall : List UInt8 → Poly256}
    {issuerA : PolyMat4} {issuerT1Scaled : PolyVec4} (issuerPk : List UInt8)
    {f : IssuerRootAttestationFields} {rootSig : ThresholdSignSig}
    (hSep : ∀ m m' w, chalHash m w = chalHash m' w → m = m')
    (hRaw : mldsaVerify chalHash sampleInBall issuerA issuerT1Scaled f.message
      rootSig.cTilde rootSig.z rootSig.h = true) :
    verifyIssuerRootAttestation chalHash sampleInBall issuerA issuerT1Scaled issuerPk f rootSig =
      false := by
  cases hNew : verifyIssuerRootAttestation chalHash sampleInBall issuerA issuerT1Scaled issuerPk
      f rootSig with
  | false => rfl
  | true =>
    unfold verifyIssuerRootAttestation at hNew
    simp only [mldsaVerify, Bool.and_eq_true, decide_eq_true_eq] at hRaw hNew
    have hEq := hSep _ _ _ (hRaw.2.symm.trans hNew.2)
    have hLen := congrArg List.length hEq
    rw [fips204MessageRepresentative_length] at hLen
    have h142 : f.message.length = 142 := encodeIssuerRootAttestationMsg_length _ _ _ _
    omega

/-! ### Ternary presentation model with issuer attestation

`BlindVcPresentation` and `verifyBlindVcPresentationTrusted` are the three-party ZKBoo
presentation (438 repetitions). The deployed selective-disclosure presentation is the 256-party
protocol of the last section; the attestation check is common to both. -/

@[expose] def BlindVcTrustedContext.attestationFields (trusted : BlindVcTrustedContext)
    (issuerPkDigest : Vec UInt8 32) : IssuerRootAttestationFields :=
  ⟨issuerPkDigest, trusted.issuerEpoch, trusted.accumulatorRoot, trusted.issuerRootTag⟩

def verifyBlindVcWithIssuerAttestation
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8) (sampleInBall : List UInt8 → Poly256)
    (issuerA : PolyMat4) (issuerT1Scaled : PolyVec4) (issuerPk : List UInt8)
    (issuerPkDigest : Vec UInt8 32) (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (trusted : BlindVcTrustedContext) (expectedSchema : VcSchema) (treeDepth : Nat)
    (verifierChallenge : List UInt8) (rootSig : ThresholdSignSig) (pres : BlindVcPresentation) : Bool :=
  verifyIssuerRootAttestation chalHash sampleInBall issuerA issuerT1Scaled issuerPk
    (trusted.attestationFields issuerPkDigest) rootSig &&
  verifyBlindVcPresentationTrusted H prgExpand .quantum128 trusted expectedSchema treeDepth verifierChallenge pres

theorem verifyBlindVcWithIssuerAttestation_eq_true_iff
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8} {sampleInBall : List UInt8 → Poly256}
    {issuerA : PolyMat4} {issuerT1Scaled : PolyVec4} {issuerPk : List UInt8}
    {issuerPkDigest : Vec UInt8 32} {H : List UInt8 → List UInt8}
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {trusted : BlindVcTrustedContext} {expectedSchema : VcSchema} {treeDepth : Nat}
    {verifierChallenge : List UInt8} {rootSig : ThresholdSignSig} {pres : BlindVcPresentation} :
    verifyBlindVcWithIssuerAttestation chalHash sampleInBall issuerA issuerT1Scaled issuerPk
      issuerPkDigest H prgExpand trusted expectedSchema treeDepth verifierChallenge rootSig pres = true ↔
    (verifyIssuerRootAttestation chalHash sampleInBall issuerA issuerT1Scaled issuerPk
      (trusted.attestationFields issuerPkDigest) rootSig = true ∧
     verifyBlindVcPresentationTrusted H prgExpand .quantum128 trusted expectedSchema treeDepth
       verifierChallenge pres = true) := by
  unfold verifyBlindVcWithIssuerAttestation; rw [Bool.and_eq_true]

structure IssuerMintedEpoch (schema : VcSchema) (treeDepth : Nat) where
  issuerPkDigest : Vec UInt8 32
  issuerRootTag : Vec UInt8 32
  epoch : UInt64
  tree : VcMerkleTree treeDepth
  mintedCreds : List (List Goldilocks × Lane4)
  hLeaves : ∀ leaf ∈ vcMerkleTreeLeaves tree,
    ∃ cred ∈ mintedCreds, computeVcPoseidon2Commit schema cred.1 cred.2 vcAttrCommitTag = some leaf

/-- The fields the issuer signed for a minted epoch. -/
@[expose] def IssuerMintedEpoch.attestationFields {schema : VcSchema} {treeDepth : Nat}
    (ep : IssuerMintedEpoch schema treeDepth) : IssuerRootAttestationFields :=
  ⟨ep.issuerPkDigest, ep.epoch, vcMerkleTreeRoot ep.epoch 0 ep.tree, ep.issuerRootTag⟩

/-- **Ternary presentation with issuer attestation: attestation of unsigned fields, collision,
or minted credential (`blindVc_presentation_reduces_to_issuer_mldsa`)**. Three consistent
accepted openings of repetition 0 of an accepted `verifyBlindVcWithIssuerAttestation` run give
one of: an accepted root attestation whose fields differ from those of the minted epoch
`epochLog`; a collision of `H`; a reachable sponge collision; a credential minted in
`epochLog` matching the disclosure. The three openings are a hypothesis: no rewinding of a
classical or quantum prover is performed here. -/
theorem blindVc_presentation_reduces_to_issuer_mldsa
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8} {sampleInBall : List UInt8 → Poly256}
    {issuerA : PolyMat4} {issuerT1Scaled : PolyVec4} {issuerPk : List UInt8}
    {issuerPkDigest : Vec UInt8 32} {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {trusted : BlindVcTrustedContext} {expectedSchema : VcSchema} {treeDepth : Nat}
    {verifierChallenge : List UInt8} {rootSig : ThresholdSignSig} {pres : BlindVcPresentation}
    (epochLog : IssuerMintedEpoch expectedSchema treeDepth) (o0 o1 o2 : OpenedBlindVcRep)
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
     trusted.attestationFields issuerPkDigest ≠ epochLog.attestationFields) ∨
    (∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂) ∨
    (∃ (c₁ c₂ : Lane6 × Lane6 × Lane6) (r : Fin 3),
      Poseidon2Perm12Sponge6Collision (spongeTrace204 c₁ r) (spongeTrace204 c₂ r)) ∨
    (∃ cred ∈ epochLog.mintedCreds, ∃ presBlind : Lane4,
      (pres.disclosedAttrs.map Prod.fst).Nodup ∧
      (∀ p ∈ pres.disclosedAttrs, p.1 < expectedSchema.arity ∧ cred.1[p.1]? = some p.2) ∧
      computeVcPoseidon2Commit expectedSchema cred.1 presBlind vcPresCommitTag = some pres.presCommit ∧
      computeVcScopeTag expectedSchema.schemaId cred.2 trusted.verifierScopeLimbs = pres.scopeTag) := by
  obtain ⟨hSigOk, hTrustedOk⟩ := verifyBlindVcWithIssuerAttestation_eq_true_iff.mp hVer
  obtain ⟨hRootEq, _, hEpEq, hScopeEq, _⟩ := verifyBlindVcPresentationTrusted_context hTrustedOk
  if hAttestMatch : trusted.attestationFields issuerPkDigest = epochLog.attestationFields then
    have hEpLog : trusted.issuerEpoch = epochLog.epoch :=
      congrArg IssuerRootAttestationFields.issuerEpoch hAttestMatch
    have hRootLog : trusted.accumulatorRoot = vcMerkleTreeRoot epochLog.epoch 0 epochLog.tree :=
      congrArg IssuerRootAttestationFields.accumulatorRoot hAttestMatch
    rcases verifyOpenedBlindVcRep_extract3_from_rewound hHLen hRew01 hRew12 hRep0 hRep1 hRep2
      with hHColl | hWit
    · exact Or.inr (Or.inl hHColl)
    · obtain ⟨attrs, hb, pb, leaf, steps, hNodup, _, hDisc, hLeaf, hSLen, hMerkle, hPres, hScope⟩ := hWit
      rw [hEpEq, hEpLog, hRootEq, hRootLog] at hMerkle
      rcases vcMerkleTree_opening_sound epochLog.epoch epochLog.tree 0 leaf steps hSLen hMerkle
        with hLeafIn | hMkColl
      · obtain ⟨cred, hCredMem, hCredLeaf⟩ := epochLog.hLeaves leaf hLeafIn
        if hSameCred : (attrs, hb) = cred then
          rcases cred with ⟨cAttrs, cHb⟩
          injection hSameCred with hAEq hHbEq; subst hAEq hHbEq; rw [← hScopeEq]
          exact Or.inr (Or.inr (Or.inr ⟨(attrs, hb), hCredMem, pb, hNodup, hDisc, hPres, hScope⟩))
        else
          have hTripleNe : (expectedSchema, attrs, hb) ≠ (expectedSchema, cred.1, cred.2) := by
            intro he; injection he with _ h2; injection h2 with ha hbEq
            exact hSameCred (Prod.ext ha hbEq)
          obtain ⟨r, hCol⟩ := blindVcReachableBinding204 expectedSchema expectedSchema
            attrs cred.1 hb cred.2 vcAttrCommitTag leaf hLeaf hCredLeaf hTripleNe
          exact Or.inr (Or.inr (Or.inl ⟨_, _, r, hCol⟩))
      · exact Or.inr (Or.inr (Or.inl hMkColl))
  else
    exact Or.inl ⟨hSigOk, hAttestMatch⟩

/-! ## §4. Opening round of the 256-party presentation in the QROM

`verify_presentation` derives the hidden parties of all `τ` repetitions as `τ` bytes squeezed
from the transcript (`VC_SD_LIMBO_OPEN`), one byte per repetition, with no modular reduction.
This section bounds that last Fiat–Shamir round alone: for a query point whose check-value
table has a nonzero entry in every repetition, at most one of the `256^τ` byte strings is
accepted by the hidden-party check (`credentialGgmCheckDefects`), and the generic
measure-and-reprogram bound `qrom_uniform_oracle_round_bound` applies with `badCard = 1`.

Scope. The nonzero check values are the hypothesis `hDefect` on doomed points; the two earlier
Fiat–Shamir rounds (folding weights, evaluation points) and commitment binding are not part of
this bound, and no claim is made about the composed three-round protocol in the QROM. The
interactive three-round count is `CutAndChoose.limbo256_tau33_defect_check_soundness`. Byte
`idx` of the challenge is digit `idx` of the challenge value in base `256`. -/

/-- Hidden-party check of all `k` repetitions on the challenge value `ch`. -/
def credentialSdOpeningAccepts (k : Nat) (defect : Nat → Fin 256 → CredentialFp5) (ch : Nat) : Bool :=
  (List.range k).all (fun idx =>
    credentialGgmCheckDefects (defect idx) ⟨(ch / 256 ^ idx) % 256, Nat.mod_lt _ (by decide)⟩)

/-- One repetition with a nonzero check value passes for at most one of the 256 bytes. -/
theorem credentialSd_rep_bad_count_le_one (defect : Fin 256 → CredentialFp5)
    (hBad : ∃ bad, defect bad ≠ credentialFp5Zero) :
    qsum 256 (fun e => if credentialGgmCheckDefects defect e = true then 1 else 0) ≤ 1 := by
  obtain ⟨bad, hBad⟩ := hBad
  exact qsum_le_one_of_subsingleton _ (fun i j hi hj =>
    (credentialGgmCheckDefects_unique defect bad hBad i hi).trans
      (credentialGgmCheckDefects_unique defect bad hBad j hj).symm)

/-- **Opening round, counting form.** With a nonzero check value in each of the `k`
    repetitions, at most one of the `256^k` challenge values is accepted. -/
theorem credentialSd_opening_bad_count_le_one (k : Nat) (defect : Nat → Fin 256 → CredentialFp5)
    (hDefect : ∀ idx < k, ∃ bad, defect idx bad ≠ credentialFp5Zero) :
    qsum (256 ^ k) (fun ch =>
      if credentialSdOpeningAccepts k defect ch.val = true then 1 else 0) ≤ 1 := by
  have h := product_bad_count_le_pow 256 1 k
    (fun idx e => credentialGgmCheckDefects (defect idx) e)
    (fun idx hlt => credentialSd_rep_bad_count_le_one (defect idx) (hDefect idx hlt))
  rw [Nat.one_pow] at h
  refine Nat.le_trans (qsum_le_qsum (fun ch => ?_)) h
  have hp : credentialSdOpeningAccepts k defect ch.val =
      (List.range k).all (fun idx =>
        if hM : 0 < 256 then
          credentialGgmCheckDefects (defect idx) ⟨(ch.val / 256 ^ idx) % 256, Nat.mod_lt _ hM⟩
        else false) := by
    unfold credentialSdOpeningAccepts
    congr 1
  rw [hp]
  exact Nat.le_refl _

/-- Acceptance of the opening round at query point `x` under oracle `O`. -/
def credentialSdOpeningLiveAfter {cardX k : Nat}
    (defect : Fin cardX → Nat → Fin 256 → CredentialFp5)
    (O : Fin cardX → BitVec (8 * k)) (x : Fin cardX) : Bool :=
  credentialSdOpeningAccepts k (defect x) (O x).toNat

/-- The opening round as a `QromRbrRound` with one bad challenge per doomed point. -/
def credentialSdOpeningQromRound {cardX k : Nat}
    (defect : Fin cardX → Nat → Fin 256 → CredentialFp5) (doomed : Fin cardX → Bool)
    (hDefect : ∀ x, doomed x = true → ∀ idx < k, ∃ bad, defect x idx bad ≠ credentialFp5Zero)
    (O : Fin cardX → BitVec (8 * k)) : QromRbrRound cardX (8 * k) O where
  proj := id
  isDoomedAt := fun _ x => doomed x
  isLiveAfter := credentialSdOpeningLiveAfter defect
  badCard := 1
  doomed_local := fun _ _ => rfl
  flip_bound := fun x hx => by
    have hPow : 2 ^ (8 * k) = 256 ^ k := Nat.pow_mul 2 8 k
    rw [qsum_cast hPow]
    refine Nat.le_trans (qsum_le_qsum (fun ch => ?_))
      (credentialSd_opening_bad_count_le_one k (defect x) (hDefect x hx))
    have hChLt : ch.1 < 2 ^ (8 * k) := by rw [hPow]; exact ch.isLt
    have hReprog : (reprogramOracle O x (BitVec.ofFin ⟨ch.1, hChLt⟩) x).toNat = ch.1 := by
      rw [reprogramOracle_self]; rfl
    show (if credentialSdOpeningAccepts k (defect x)
        (reprogramOracle O x (BitVec.ofFin ⟨ch.1, hChLt⟩) x).toNat = true then 1 else 0) ≤ _
    rw [hReprog]
    exact Nat.le_refl _

/-- Query budget against the `33`-byte opening challenge: for `Q ≤ 2^60`,
    `(2Q + 1)^2 · 2^128 < 256^33`. -/
theorem credentialSd_opening_qrom_budget (Q : Nat) (hQ : Q ≤ 2 ^ 60) :
    (2 * Q + 1) ^ 2 * 2 ^ 128 < (256 : Nat) ^ 33 := by
  have hm := Nat.mul_le_mul_right (2 ^ 128)
    (Nat.pow_le_pow_left (show 2 * Q + 1 ≤ 2 * 2 ^ 60 + 1 by omega) 2)
  exact Nat.lt_of_le_of_lt hm (by decide +kernel)

/-- **Opening round of the 33-repetition presentation, QROM query-mass bound
    (`credentialSd_opening_round_qrom_bound`)**. For a `Q`-query quantum adversary and a uniform
    oracle with `33`-byte outputs, the ordinary doomed-to-live flip mass of the opening round is
    at most `(2Q + 1)^2 / 2^264`, where a point is doomed only if its check-value table has a
    nonzero entry in every repetition (`hDefect`); for `Q ≤ 2^60` that is below `2^-128`. -/
theorem credentialSd_opening_round_qrom_bound
    {cardX cardAnc Q : Nat} (hQ : Q ≤ 2 ^ 60)
    (A : QuantumAdv cardX (8 * 33) cardAnc Q)
    (defect : Fin cardX → Nat → Fin 256 → CredentialFp5) (doomed : Fin cardX → Bool)
    (hDefect : ∀ x, doomed x = true → ∀ idx < 33, ∃ bad, defect x idx bad ≠ credentialFp5Zero) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    RatBound.le
      ⟨uniformOracleSum (8 * 33) cardX
         (fun O => qromOrdinaryFlipMass A O id (fun _ x => doomed x)
           (credentialSdOpeningLiveAfter defect)),
       (2 ^ (8 * 33)) ^ cardX * norm,
       Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos _))
         (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * 1, 2 ^ (8 * 33), Nat.two_pow_pos _⟩ ∧
    (2 * Q + 1) ^ 2 * 2 ^ 128 < (256 : Nat) ^ 33 ∧
    credentialSdRepetitions = 33 :=
  ⟨qrom_uniform_oracle_round_bound A
    (credentialSdOpeningQromRound defect doomed hDefect)
    id (fun _ x => doomed x) (credentialSdOpeningLiveAfter defect)
    1 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
    credentialSd_opening_qrom_budget Q hQ, credentialSdRepetitions_eq⟩

/-- Consistent copies never trigger the finite collision event, for any hash. -/
theorem vcRewoundCommitConflict_consistent_table
    (H : List UInt8 → List UInt8) (nonce : Vec UInt8 32) (idx : Nat) (o : OpenedBlindVcRep) :
    let clean := { o with viewE1 := o.viewE }
    ¬ VcRewoundCommitConflict H nonce idx clean clean clean := by
  intro clean
  simp only [VcRewoundCommitConflict, clean, ne_eq, not_true_eq_false, false_and, or_self,
    not_false_eq_true]

theorem blindVc_collision_filter_preserves_honest_openings
    (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmt : BlindVcPublicStatement) (idx : Nat)
    (r1 : Triple3 (List UInt8) × VcRepFinalOuts3) (tr : BlindVcRepTriple) (e : Fin 3) :
    verifyCollisionFreeCommittedBlindVcRep H prgExpand stmt idx r1
      (openBlindVcRep H stmt.presNonce idx tr) e =
    verifyCommittedBlindVcRep H prgExpand stmt idx r1 e
      (openBlindVcRep H stmt.presNonce idx tr e) := by
  simp only [verifyCollisionFreeCommittedBlindVcRep,
    vcRewoundCommitConflict_honest_table, decide_false, Bool.not_false, Bool.true_and]

#verify_constructive vcRewoundCommitConflict_consistent_table
  blindVc_committed_acceptance_decomposition blindVcTableConflict_extract
  blindVc_fs_acceptance_decomposition
  blindVc_collision_filter_preserves_honest_openings blindVcWitnessValid_of_extraction

#verify_constructive blindVc_rep_pigeonhole_le_two blindVc_quantum128_interactive_rbr_bound
  word64_mod3_bad_count_le blindVc_qrom_fs_round_bound blindVc_quantum128_qrom_fs_soundness
  evalVcMerklePathBool_eq_merkleRootFromPath vcMerkleTree_opening_sound
  encodeIssuerRootAttestationMsg_length encodeIssuerRootAttestationMsg_injective
  credentialSd_rep_bad_count_le_one credentialSd_opening_bad_count_le_one
  credentialSd_opening_qrom_budget credentialSd_opening_round_qrom_bound
  IssuerRootAttestationFields.message_injective verifyIssuerRootAttestationBytes_accepts_core
  verifyIssuerRootAttestation_rejects_raw_message_signature
  blindVc_presentation_reduces_to_issuer_mldsa

end Qsag
