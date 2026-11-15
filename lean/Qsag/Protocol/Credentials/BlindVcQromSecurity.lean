module
/-
# BlindVC 438-Repetition Multi-Round QROM Fiat-Shamir & Issuer-Binding Security

Constructive Lean 4.35 bounds for the collision-filtered, supplied-opening-table model
of `BlindVC` (`Quantum128`, `438` ZKBoo repetitions). The language is actual credential
witness validity. `VcRewoundCommitConflict` records an actual pair of conflicting committed
views in the finite supplied table, and `blindVc_committed_acceptance_decomposition`
accounts for the omitted event. Bounding that event computationally, constructing the
three-opening table from a quantum prover, and linking measured-query mass to the output
forgery event remain separate obligations. There is no global collision-freedom premise.
1. **Interactive `438`-Repetition ZKBoo `PublicCoinIop` & `RbrStateFunction`
   (`blindVcParallelRbr`, `blindVc_quantum128_interactive_rbr_bound`)**:
   Ternary pigeonhole across `438` committed repetitions (`2^438 * 2^256 < 3^438`, `> 128` Grover
   bits) composed with adaptive state-restoration (`rbr_implies_state_restoration_soundness`).
2. **Multi-Round QROM Fiat-Shamir (`blindVcQromFsRound`, `blindVc_quantum128_qrom_fs_soundness`)**:
   Exact `64`-bit modulo-`3` squeeze (`blindVcBadWord64 = 12297829382473034411` out of `2^64`),
   proving `(2 * Q + 1)^2 * blindVcBadWord64^438 * 2^128 < (2^64)^438` for all `Q ≤ 2^60`.
3. **Merkle Path Bridge & Issuer `ML-DSA` Root-Attestation Unforgeability
   (`evalVcMerklePathBool_eq_merkleRootFromPath`, `blindVc_presentation_reduces_to_issuer_mldsa`)**:
   Bridges `evalVcMerklePathBool` to `merkleRootFromPath`, proves `vcMerkleTree_opening_sound`,
   and gives an issuer-attestation/collision/witness disjunction given three consistent
   accepted openings. Fresh-message EUF-CMA and quantum extraction are separate games.
-/

public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
public import Qsag.Oracle.MultiRoundFsQrom
public import Qsag.Tactic.AssuranceKit
import all Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
import all Qsag.Oracle.MultiRoundFsQrom
import all Qsag.Oracle.ConcreteSecurityBudget
import all Qsag.Oracle.UcGames
import all Qsag.Protocol.Credentials.AdvancedMpcAndCreds
import all Qsag.Math.Goldilocks

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

private def vecOfListLen {α : Type} : (xs : List α) → {n : Nat} → xs.length = n → Vec α n
  | [], 0, _ => .nil
  | x :: xs, _ + 1, h => .cons x (vecOfListLen xs (Nat.succ.inj h))

private theorem vecOfListLen_toList {α : Type} : ∀ (xs : List α) {n : Nat} (h : xs.length = n),
    (vecOfListLen xs h).toList = xs
  | [], 0, _ => rfl
  | _ :: xs, _ + 1, h => by simp [vecOfListLen, Vec.toList, vecOfListLen_toList xs (Nat.succ.inj h)]

/-! ## §1. `438`-Repetition `BlindVC` ZKBoo `PublicCoinIop` & `RbrStateFunction` -/

def fin3AllTrue (p : Fin 3 → Bool) : Bool := p 0 && p 1 && p 2

theorem fin3_not_all_count_le_two (p : Fin 3 → Bool)
    (hNotAll : fin3AllTrue p = false) :
    qsum 3 (fun e => if p e = true then 1 else 0) ≤ 2 := by
  unfold fin3AllTrue at hNotAll
  simp only [qsum, Nat.add_zero]
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
      have hAsc : vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs = true := by
        unfold verifyOpenedBlindVcRep at hV0; dsimp only at hV0
        cases hG :
            (decide ((cand 0).e = 0) &&
             vcCheckDisclosedStrictAsc stmt.schema.arity stmt.disclosedAttrs &&
             decide ((cand 0).viewE.attrShares.length = stmt.schema.arity) &&
             decide ((cand 0).viewE1.attrShares.length = stmt.schema.arity) &&
             decide ((cand 0).viewE.merkleLevels.length = stmt.treeDepth) &&
             decide ((cand 0).viewE1.merkleLevels.length = stmt.treeDepth) &&
             vcCheckPartyDisclosedShares (cand 0).e (cand 0).viewE.attrShares stmt.disclosedAttrs &&
             vcCheckPartyDisclosedShares (vcNextParty3 (cand 0).e) (cand 0).viewE1.attrShares stmt.disclosedAttrs &&
             checkPartyPrgTape prgExpand stmt.treeDepth repIdx (cand 0).e (cand 0).viewE &&
             checkPartyPrgTape prgExpand stmt.treeDepth repIdx (vcNextParty3 (cand 0).e) (cand 0).viewE1) with
        | false => rw [hG] at hV0; cases hV0
        | true => simp only [Bool.and_eq_true] at hG; exact hG.1.1.1.1.1.1.1.1.2
      let wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth :=
        { attrs := vecOfListLen attrs hAr, holderBlind := hb, presBlind := pb,
          merkleSteps := vecOfListLen steps hSLen }
      have hVal : BlindVcWitnessValid stmt wit := by
        unfold BlindVcWitnessValid
        refine ⟨hAsc, fun p hp => ?_, ⟨leaf, ?_, ?_⟩, ?_, hScope⟩
        · rw [vecOfListLen_toList attrs hAr]; exact (hDisc p hp).2
        · rw [vecOfListLen_toList attrs hAr]; exact hLeaf
        · rw [vecOfListLen_toList steps hSLen]; exact hRoot
        · rw [vecOfListLen_toList attrs hAr]; exact hPres
      exact False.elim (hNoWit ⟨wit, hVal⟩)

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
    rw [qsum_cast (Nat.zero_add Y) g]; simp only [qsum, Nat.zero_add]
  | X + 1, Y, g => by
    have hEq : X + 1 + Y = (X + Y) + 1 := by omega
    rw [qsum_cast hEq g]
    have ih := qsum_add_split_local X Y (fun z => g ⟨z.1 + 1, by omega⟩)
    simp only [qsum]
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
  | 0, B, f => by rw [qsum_cast (Nat.zero_mul B) f]; rfl
  | A + 1, B, f => by
    have hAB : (A + 1) * B = B + A * B := by rw [Nat.succ_mul, Nat.add_comm]
    rw [qsum_cast hAB f, qsum_add_split_local B (A * B),
        qsum_mul_factor A B (fun k => f ⟨B + k.1, by omega⟩)]
    conv => rhs; unfold qsum
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
  | 0, _, _ => Nat.le_refl 1
  | k + 1, p, hEach => by
    if hM0 : M = 0 then
      subst hM0; rw [Nat.zero_pow (Nat.succ_pos k)]; exact Nat.zero_le _
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
    simp only [qsum, Nat.add_zero]
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
