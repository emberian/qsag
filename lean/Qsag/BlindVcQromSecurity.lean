module
/-
# BlindVC 438-Repetition Multi-Round QROM Fiat-Shamir & Issuer-Binding Security

Constructive Lean 4.35 composition closing `BlindVC` (`Quantum128`, `438` ZKBoo repetitions)
against `Qsag.MultiRoundFsQrom` and `Qsag.ThresholdMlDsaAndToprf`:
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
   and reduces `verifyBlindVcWithIssuerAttestation` tightly to issuer `ML-DSA` forgery or collision.
-/

public import Qsag.ThresholdMlDsaAndToprf
public import Qsag.MultiRoundFsQrom
public import Qsag.Tactic.AssuranceKit
import all Qsag.ThresholdMlDsaAndToprf
import all Qsag.MultiRoundFsQrom
import all Qsag.ConcreteSecurityBudget
import all Qsag.UcGames
import all Qsag.AdvancedMpcAndCreds
import all Qsag.Goldilocks

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

/-- **Per-Repetition 3-Challenge Pigeonhole Soundness (`blindVc_rep_pigeonhole_le_two`)**:
    Without an `H`-collision or valid `BlindVcSecretWitness`, at most `2` of `3` challenges accept. -/
theorem blindVc_rep_pigeonhole_le_two
    {H : List UInt8 → List UInt8} (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (hNoColl : ¬ ∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {stmt : BlindVcPublicStatement}
    (hNoWit : ¬ ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth,
      BlindVcWitnessValid stmt wit)
    (repIdx : Nat) (r1 : Triple3 (List UInt8) × VcRepFinalOuts3)
    (cand : Fin 3 → OpenedBlindVcRep) :
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
    rcases verifyOpenedBlindVcRep_extract3_from_rewound hHLen
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
    (∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂) ∨
    (∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth, BlindVcWitnessValid stmt wit)
  verify := fun stmt tr =>
    match tr with
    | [(msg, ch)] =>
      (List.range k).all (fun idx =>
        if hIdx : idx < k then
          let fi : Fin k := ⟨idx, hIdx⟩
          let e := decodeTernaryChallengeAt ch idx
          verifyCommittedBlindVcRep H prgExpand stmt idx (Vec.get msg.allRound1 fi) e
            ((Vec.get msg.openTable fi).get e)
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
      have hNoColl : ¬ ∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂ := fun hc => hDoomed (.inl hc)
      have hNoWit : ¬ ∃ wit : BlindVcSecretWitness stmt.schema.arity stmt.treeDepth,
          BlindVcWitnessValid stmt wit := fun hw => hDoomed (.inr hw)
      let p : Nat → Fin 3 → Bool := fun idx e =>
        if hIdx : idx < k then
          verifyCommittedBlindVcRep H prgExpand stmt idx (Vec.get msg.allRound1 ⟨idx, hIdx⟩) e
            ((Vec.get msg.openTable ⟨idx, hIdx⟩).get e)
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
            verifyCommittedBlindVcRep H prgExpand stmt idx (Vec.get msg.allRound1 ⟨idx, hlt⟩) e
              ((Vec.get msg.openTable ⟨idx, hlt⟩).get e) := fun _ => dite_true hlt _ _
        rw [qsum_congr (fun e => by rw [hP e])]
        exact blindVc_rep_pigeonhole_le_two hHLen hNoColl hNoWit idx
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
      verifyCommittedBlindVcRep H_hash prgExpand (stmtAt x) idx
        (Vec.get (msgAt x).allRound1 fi) e ((Vec.get (msgAt x).openTable fi).get e)
    else true)

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
    have hNoColl : ¬ ∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H_hash m₁ = H_hash m₂ := fun hc => hNotIn (.inl hc)
    have hNoWit : ¬ ∃ wit : BlindVcSecretWitness (stmtAt x).schema.arity (stmtAt x).treeDepth,
        BlindVcWitnessValid (stmtAt x) wit := fun hw => hNotIn (.inr hw)
    let p : Nat → Fin (2 ^ 64) → Bool := fun idx u =>
      if hIdx : idx < k then
        let fi : Fin k := ⟨idx, hIdx⟩
        let e : Fin 3 := ⟨u.1 % 3, Nat.mod_lt _ (by decide)⟩
        verifyCommittedBlindVcRep H_hash prgExpand (stmtAt x) idx
          (Vec.get (msgAt x).allRound1 fi) e ((Vec.get (msgAt x).openTable fi).get e)
      else true
    have hEach : ∀ idx < k, qsum (2 ^ 64) (fun u => if p idx u = true then 1 else 0) ≤
        blindVcBadWord64 := by
      intro idx hlt
      let fi : Fin k := ⟨idx, hlt⟩
      let q3 : Fin 3 → Bool := fun e =>
        verifyCommittedBlindVcRep H_hash prgExpand (stmtAt x) idx
          (Vec.get (msgAt x).allRound1 fi) e ((Vec.get (msgAt x).openTable fi).get e)
      have hNotAll3 : fin3AllTrue q3 = false := by
        unfold fin3AllTrue
        cases hAll : (q3 0 && q3 1 && q3 2) with
        | false => rfl
        | true =>
          have h3 : qsum 3 (fun e => if q3 e = true then 1 else 0) = 3 := by
            simp only [Bool.and_eq_true] at hAll; rcases hAll with ⟨⟨h0, h1⟩, h2⟩
            simp only [qsum, Nat.add_zero]
            change (if q3 0 = true then 1 else 0) +
              ((if q3 1 = true then 1 else 0) + (if q3 2 = true then 1 else 0)) = 3
            rw [h0, h1, h2]; decide
          have hLe2 := blindVc_rep_pigeonhole_le_two (prgExpand := prgExpand) hHLen hNoColl hNoWit idx
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
      unfold reprogramOracle; rw [ite_true rfl]; rfl
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
    Bounds unitary `Q`-query QROM forgery by `(2 * Q + 1)^2 * blindVcBadWord64^438 / 2^(64 * 438)`,
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
  | _, _, [] => rfl
  | layer, cur, (false, _) :: rest => by
    simp only [evalVcMerklePathBool, vcBoolStepsIdx, List.map, merkleRootFromPath,
      Bool.false_eq_true, ↓reduceIte]
    have hMod : (0 + 2 * vcBoolStepsIdx rest) % 2 = 0 := by omega
    have hDiv : (0 + 2 * vcBoolStepsIdx rest) / 2 = vcBoolStepsIdx rest := by omega
    rw [ite_true hMod, hDiv]
    exact evalVcMerklePathBool_eq_merkleRootFromPath epoch (layer + 1) _ rest
  | layer, cur, (true, _) :: rest => by
    simp only [evalVcMerklePathBool, vcBoolStepsIdx, List.map, merkleRootFromPath, ↓reduceIte]
    have hMod : (1 + 2 * vcBoolStepsIdx rest) % 2 ≠ 0 := by omega
    have hDiv : (1 + 2 * vcBoolStepsIdx rest) / 2 = vcBoolStepsIdx rest := by omega
    rw [ite_false hMod, hDiv]
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
  | [], _, _, false, _ => by simp [evalVcMerklePathBool]
  | [], _, _, true, _ => by simp [evalVcMerklePathBool]
  | (b0, _) :: rest, layer, _, b, sib => by
    cases b0 <;> dsimp only [List.cons_append, evalVcMerklePathBool, List.length_cons] <;>
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
    Or.inl (by dsimp [evalVcMerklePathBool, vcMerkleTreeRoot] at hEq; rw [hEq]; exact .head [])
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
          fun hc => hChildren ⟨congrArg Prod.fst hc, congrArg (fun p => p.2.1) hc⟩
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
          fun hc => hChildren ⟨congrArg Prod.fst hc, congrArg (fun p => p.2.1) hc⟩
        obtain ⟨r, hCol⟩ := absorbRate6Sponge3_reachable_collision204 hChunksNe hEq
        exact Or.inr ⟨_, _, r, hCol⟩

def encodeIssuerRootAttestationMsg (issuerRootTag : Vec UInt8 32) (epoch : UInt64) (accRoot : Lane6) : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x4F, 0x4F, 0x54] ++
  issuerRootTag.toList ++ encodeNatLeBytes 8 epoch.toNat ++
  encodeGoldilocksVecLe [accRoot.x0, accRoot.x1, accRoot.x2, accRoot.x3, accRoot.x4, accRoot.x5]

def verifyBlindVcWithIssuerAttestation
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8) (sampleInBall : List UInt8 → Poly256)
    (issuerA : PolyMat4) (issuerT1Scaled : PolyVec4) (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (trusted : BlindVcTrustedContext) (expectedSchema : VcSchema) (treeDepth : Nat)
    (verifierChallenge : List UInt8) (rootSig : ThresholdSignSig) (pres : BlindVcPresentation) : Bool :=
  mldsaVerify chalHash sampleInBall issuerA issuerT1Scaled
    (encodeIssuerRootAttestationMsg trusted.issuerRootTag trusted.issuerEpoch trusted.accumulatorRoot)
    rootSig.cTilde rootSig.z rootSig.h &&
  verifyBlindVcPresentationTrusted H prgExpand .quantum128 trusted expectedSchema treeDepth verifierChallenge pres

structure IssuerMintedEpoch (schema : VcSchema) (treeDepth : Nat) where
  issuerRootTag : Vec UInt8 32
  epoch : UInt64
  tree : VcMerkleTree treeDepth
  mintedCreds : List (List Goldilocks × Lane4)
  hLeaves : ∀ leaf ∈ vcMerkleTreeLeaves tree,
    ∃ cred ∈ mintedCreds, computeVcPoseidon2Commit schema cred.1 cred.2 vcAttrCommitTag = some leaf

/-- **End-to-End `BlindVC` -> Issuer `ML-DSA` Unforgeability & Collision Reduction
    (`blindVc_presentation_reduces_to_issuer_mldsa`)**. -/
theorem blindVc_presentation_reduces_to_issuer_mldsa
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8} {sampleInBall : List UInt8 → Poly256}
    {issuerA : PolyMat4} {issuerT1Scaled : PolyVec4} {H : List UInt8 → List UInt8}
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    {prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D}
    {trusted : BlindVcTrustedContext} {expectedSchema : VcSchema} {treeDepth : Nat}
    {verifierChallenge : List UInt8} {rootSig : ThresholdSignSig} {pres : BlindVcPresentation}
    (epochLog : IssuerMintedEpoch expectedSchema treeDepth) (o0 o1 o2 : OpenedBlindVcRep)
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
    (mldsaVerify chalHash sampleInBall issuerA issuerT1Scaled
       (encodeIssuerRootAttestationMsg trusted.issuerRootTag trusted.issuerEpoch trusted.accumulatorRoot)
       rootSig.cTilde rootSig.z rootSig.h = true ∧
     (trusted.issuerRootTag ≠ epochLog.issuerRootTag ∨ trusted.issuerEpoch ≠ epochLog.epoch ∨
      trusted.accumulatorRoot ≠ vcMerkleTreeRoot epochLog.epoch 0 epochLog.tree)) ∨
    (∃ m₁ m₂ : List UInt8, m₁ ≠ m₂ ∧ H m₁ = H m₂) ∨
    (∃ (c₁ c₂ : Lane6 × Lane6 × Lane6) (r : Fin 3),
      Poseidon2Perm12Sponge6Collision (spongeTrace204 c₁ r) (spongeTrace204 c₂ r)) ∨
    (∃ cred ∈ epochLog.mintedCreds, ∃ presBlind : Lane4,
      (pres.disclosedAttrs.map Prod.fst).Nodup ∧
      (∀ p ∈ pres.disclosedAttrs, p.1 < expectedSchema.arity ∧ cred.1[p.1]? = some p.2) ∧
      computeVcPoseidon2Commit expectedSchema cred.1 presBlind vcPresCommitTag = some pres.presCommit ∧
      computeVcScopeTag expectedSchema.schemaId cred.2 trusted.verifierScopeLimbs = pres.scopeTag) := by
  unfold verifyBlindVcWithIssuerAttestation at hVer
  rw [Bool.and_eq_true] at hVer; obtain ⟨hSigOk, hTrustedOk⟩ := hVer
  obtain ⟨hRootEq, _, hEpEq, hScopeEq, _⟩ := verifyBlindVcPresentationTrusted_context hTrustedOk
  if hAttestMatch :
      trusted.issuerRootTag = epochLog.issuerRootTag ∧ trusted.issuerEpoch = epochLog.epoch ∧
      trusted.accumulatorRoot = vcMerkleTreeRoot epochLog.epoch 0 epochLog.tree then
    obtain ⟨_, hEpLog, hRootLog⟩ := hAttestMatch
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
    left; refine ⟨hSigOk, ?_⟩
    if h1 : trusted.issuerRootTag = epochLog.issuerRootTag then
      if h2 : trusted.issuerEpoch = epochLog.epoch then
        exact Or.inr (Or.inr fun h3 => hAttestMatch ⟨h1, h2, h3⟩)
      else exact Or.inr (Or.inl h2)
    else exact Or.inl h1

theorem tooth_blindVc_unsigned_issuer_root_rejected
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8) (sampleInBall : List UInt8 → Poly256)
    (issuerA : PolyMat4) (issuerT1Scaled : PolyVec4) (H : List UInt8 → List UInt8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (trusted : BlindVcTrustedContext) (expectedSchema : VcSchema) (treeDepth : Nat)
    (verifierChallenge : List UInt8) (rootSig : ThresholdSignSig) (pres : BlindVcPresentation)
    (hBadSig : mldsaVerify chalHash sampleInBall issuerA issuerT1Scaled
      (encodeIssuerRootAttestationMsg trusted.issuerRootTag trusted.issuerEpoch trusted.accumulatorRoot)
      rootSig.cTilde rootSig.z rootSig.h = false) :
    verifyBlindVcWithIssuerAttestation chalHash sampleInBall issuerA issuerT1Scaled
      H prgExpand trusted expectedSchema treeDepth verifierChallenge rootSig pres = false := by
  unfold verifyBlindVcWithIssuerAttestation; rw [hBadSig, Bool.false_and]

theorem tooth_single_rep_two_of_three_tight :
    ∃ p : Fin 3 → Bool, fin3AllTrue p = false ∧
      qsum 3 (fun e => if p e = true then 1 else 0) = 2 ∧ ¬ (2 ^ 1 * 2 ^ 1 < 3 ^ 1) :=
  ⟨fun e => decide (e.1 < 2), by decide, by decide, by decide⟩

theorem fin3_not_all_count_witness :
    ∃ p : Fin 3 → Bool, fin3AllTrue p = false ∧
      qsum 3 (fun e => if p e = true then 1 else 0) ≤ 2 :=
  ⟨fun e => decide (e.1 < 2), by decide, by decide⟩

theorem vcMerkleTree_opening_witness :
    ∃ (epoch : UInt64) (tree : VcMerkleTree 0) (layer : Nat) (leaf : Lane6) (steps : List (Bool × Lane6)),
      steps.length = 0 ∧ evalVcMerklePathBool epoch layer leaf steps = vcMerkleTreeRoot epoch layer tree :=
  let z6 : Lane6 :=
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  ⟨0, .leaf z6, 0, z6, [], rfl, rfl⟩

#verify_constructive blindVc_rep_pigeonhole_le_two blindVc_quantum128_interactive_rbr_bound
  word64_mod3_bad_count_le blindVc_qrom_fs_round_bound blindVc_quantum128_qrom_fs_soundness
  evalVcMerklePathBool_eq_merkleRootFromPath vcMerkleTree_opening_sound
  blindVc_presentation_reduces_to_issuer_mldsa
#tooth_pair fin3_not_all_count_le_two vs tooth_single_rep_two_of_three_tight
#verify_inhabited fin3_not_all_count_le_two fin3_not_all_count_witness
#tooth_pair word64_mod3_bad_count_le vs tooth_single_rep_two_of_three_tight
#verify_inhabited word64_mod3_bad_count_le fin3_not_all_count_witness
#verify_inhabited vcMerkleTree_opening_sound vcMerkleTree_opening_witness
#tooth_pair blindVc_presentation_reduces_to_issuer_mldsa vs tooth_blindVc_unsigned_issuer_root_rejected

end Qsag
