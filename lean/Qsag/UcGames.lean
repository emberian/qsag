module
/-
# Qsag.UcGames — Finite `KeyedLazyRO`, Shamir Pad-Space Bijections & Canetti UC Signatures

Self-contained Lean 4.35 game-hopping, secret-sharing simulation, and UC signature foundations:
1. Finite query-bounded `OracleComp` decision trees, slice reprogramming (`condProb_pin_untouched`),
   unified leaf+Merkle birthday bound (`unifiedTreeGame_birthday_le`), keyed-ROM hiding floor
   (`hidingAdv_le`, `hidingAdv_le_deployed`) at exact deployed cardinalities (`2^256` vs `p^4`,
   `deployedCardGoldilocks4_ne_bitVec256`), and 3-regime query characterization
   (`lazyRo_query_regime_characterization`).
2. Polymorphic Shamir pad-space bijection (`shamir_rebalanceEquiv`,
   `pad_bijection_masked_openings_uniform`) over `Goldilocks`, `GoldilocksExt2`, and `TowerElem k`
   with characteristic-2 involution (`shamir_tower_rebalance_involutive`), collusion threshold teeth
   (`full_collusion_breaks_hiding`, `unpadded_open_refutes_hiding`), and Vandermonde-at-zero
   reconstruction (`lagrangeAtZero_evalCoeffs`).
3. Canetti UC signature functionality `idealSig` (`ucRealizes_iff_eufCma`), multi-session hybrid
   telescope (`multi_session_uc_realizes`), and universal composition (`uc_composition_theorem`).
-/

public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Poseidon2

public section
namespace Qsag

set_option autoImplicit false

/-- Equality of finite indices is decided directly by their natural values. -/
instance (priority := 2000) constructiveFinDecidableEq (n : Nat) : DecidableEq (Fin n) :=
  fun a b =>
    if h : a.val = b.val then .isTrue (Fin.ext h)
    else .isFalse (fun he => h (congrArg Fin.val he))

instance (priority := 2000) constructiveFinBEq (n : Nat) : BEq (Fin n) where
  beq a b := a.val == b.val

instance (priority := 2000) constructiveFinLawfulBEq (n : Nat) : LawfulBEq (Fin n) where
  eq_of_beq h := Fin.ext (Nat.eq_of_beq_eq_true h)
  rfl := Nat.beq_refl _



/-! ## 1. Rational Probability Bounds, `OracleComp` & `KeyedLazyRO` Floors -/

/-- Exact cross-multiplied rational inequality `a.1 / a.2 ≤ b.1 / b.2` with mandatory positive denominators (`0 < a.2 ∧ 0 < b.2`). -/
@[expose] def ratLe (a b : Nat × Nat) : Prop :=
  0 < a.2 ∧ 0 < b.2 ∧ a.1 * b.2 ≤ b.1 * a.2

theorem ratLe_zero_den_false (a b c : Nat) : ¬ ratLe (a, 0) (b, c) ∧ ¬ ratLe (a, c) (b, 0) := by
  constructor
  · intro h; exact Nat.not_lt_zero _ h.1
  · intro h; exact Nat.not_lt_zero _ h.2.1

@[expose] def deployedCardBitVec256 : Nat := 2 ^ 256
@[expose] def deployedCardGoldilocks4 : Nat := goldilocksPrime ^ 4

theorem deployedCardGoldilocks4_ne_bitVec256 :
    deployedCardGoldilocks4 ≠ deployedCardBitVec256 ∧
    2 ^ 255 < deployedCardGoldilocks4 ∧
    deployedCardGoldilocks4 < deployedCardBitVec256 := by
  unfold deployedCardGoldilocks4 deployedCardBitVec256
  decide

def finSum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + finSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem finSum_const : ∀ (n c : Nat), finSum n (fun _ => c) = n * c
  | 0, _ => by simp [finSum]
  | n + 1, c => by
    simp only [finSum, finSum_const n c, Nat.succ_mul]
    omega

theorem finSum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum, h ⟨0, Nat.zero_lt_succ n⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem finSum_le_finSum {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    finSum n f ≤ finSum n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [finSum]
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    have hRest := ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

theorem finSum_add {n : Nat} (f g : Fin n → Nat) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finSum, ih]
    omega

theorem finSum_eq_indicator : ∀ (n : Nat) (a : Fin n),
    finSum n (fun i => if i = a then 1 else 0) = 1
  | 0, a => Fin.elim0 a
  | n + 1, ⟨0, _⟩ => by
    simp only [finSum, ↓reduceIte]
    have hZero : finSum n (fun i => if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) =
        finSum n (fun _ => 0) := by
      apply finSum_congr
      intro i
      have hNe : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨0, Nat.zero_lt_succ n⟩ := by
        intro he
        have hv := congrArg Fin.val he
        exact Nat.noConfusion hv
      simp only [hNe, ↓reduceIte]
    rw [hZero, finSum_const]
    omega
  | n + 1, ⟨k + 1, hk⟩ => by
    simp only [finSum]
    have h0 : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ := by
      intro heq
      have hv := congrArg Fin.val heq
      exact Nat.noConfusion hv
    simp only [h0, ↓reduceIte, Nat.zero_add]
    have hShift :
        finSum n (fun i => if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩ then 1 else 0) =
        finSum n (fun i => if i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ then 1 else 0) := by
      apply finSum_congr
      intro i
      by_cases hik : i.1 = k
      · have h2 : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hik
        simp only [h2, ↓reduceIte]
      · have h2 : i ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := fun heq => hik (congrArg Fin.val heq)
        have h1 : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ := fun heq =>
          hik (Nat.succ.inj (congrArg Fin.val heq))
        rw [ite_eq_right_iff.mpr (fun h => False.elim (h1 h)),
            ite_eq_right_iff.mpr (fun h => False.elim (h2 h))]
    rw [hShift]
    exact finSum_eq_indicator n ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem finSum_mem_list_le (n : Nat) : ∀ (S : List (Fin n)),
    finSum n (fun i => if i ∈ S then 1 else 0) ≤ S.length
  | [] => by
    have h0 : finSum n (fun i => if i ∈ ([] : List (Fin n)) then 1 else 0) = finSum n (fun _ => 0) :=
      finSum_congr (fun _ => rfl)
    rw [h0, finSum_const]
    omega
  | a :: S => by
    have hPoint : ∀ i : Fin n,
        (if i ∈ a :: S then 1 else 0) ≤ (if i = a then 1 else 0) + (if i ∈ S then 1 else 0) := by
      intro i
      by_cases hia : i = a
      · subst hia; simp
      · by_cases his : i ∈ S <;> simp [hia, his]
    have hLe := finSum_le_finSum hPoint
    rw [finSum_add, finSum_eq_indicator] at hLe
    have ih := finSum_mem_list_le n S
    simp only [List.length_cons]
    omega

def natAbsDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

theorem natAbsDiff_triangle (a b c : Nat) :
    natAbsDiff a c ≤ natAbsDiff a b + natAbsDiff b c := by
  unfold natAbsDiff
  split <;> split <;> split <;> omega

private theorem natAbsDiff_step (p0 q0 sp sq sb : Nat)
    (hp0 : p0 ≤ 1) (hq0 : q0 ≤ 1) (hih : natAbsDiff sp sq ≤ sb) :
    natAbsDiff (p0 + sp) (q0 + sq) ≤ 1 + sb := by
  unfold natAbsDiff at hih ⊢
  split at hih <;> split <;> omega

private theorem natAbsDiff_same_add (v sp sq : Nat) :
    natAbsDiff (v + sp) (v + sq) = natAbsDiff sp sq := by
  unfold natAbsDiff
  split <;> split <;> omega

theorem finSum_indicator_diff_le {n : Nat} (p q : Fin n → Bool) (bad : Fin n → Bool)
    (hAgree : ∀ i : Fin n, bad i = false → p i = q i) :
    natAbsDiff (finSum n (fun i => if p i then 1 else 0))
               (finSum n (fun i => if q i then 1 else 0)) ≤
      finSum n (fun i => if bad i then 1 else 0) := by
  induction n with
  | zero => simp [finSum, natAbsDiff]
  | succ n ih =>
    simp only [finSum]
    let p' : Fin n → Bool := fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let q' : Fin n → Bool := fun i => q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let b' : Fin n → Bool := fun i => bad ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have ih' := ih p' q' b' (fun i hi => hAgree ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ hi)
    cases hb0 : bad ⟨0, Nat.zero_lt_succ n⟩
    · have hpq0 := hAgree ⟨0, Nat.zero_lt_succ n⟩ hb0
      rw [hpq0]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, natAbsDiff_same_add]
      exact ih'
    · simp only [↓reduceIte]
      exact natAbsDiff_step _ _ _ _ _
        (by split <;> omega) (by split <;> omega) ih'

inductive OracleComp (Dom Cod α : Type) where
  | pure (ret : α)
  | query (q : Dom) (next : Cod → OracleComp Dom Cod α)

@[expose] def evalOracleComp {Dom Cod α : Type} (O : Dom → Cod) : OracleComp Dom Cod α → α
  | .pure ret => ret
  | .query q next => evalOracleComp O (next (O q))

def queryLog {Dom Cod α : Type} (O : Dom → Cod) : OracleComp Dom Cod α → List Dom
  | .pure _ => []
  | .query q next => q :: queryLog O (next (O q))

def QueryBounded {Dom Cod α : Type} : Nat → OracleComp Dom Cod α → Prop
  | _, .pure _ => True
  | 0, .query _ _ => False
  | Q + 1, .query _ next => ∀ y : Cod, QueryBounded Q (next y)

theorem queryLog_length_le {Dom Cod α : Type} (O : Dom → Cod) :
    ∀ {Q : Nat} {prog : OracleComp Dom Cod α}, QueryBounded Q prog → (queryLog O prog).length ≤ Q
  | _, .pure _, _ => Nat.zero_le _
  | 0, .query _ _, h => False.elim h
  | Q + 1, .query q next, h => by
    simp only [queryLog, List.length_cons]
    have ih := queryLog_length_le O (h (O q))
    omega

def pinOracle {Dom Cod : Type} [DecidableEq Dom] (O : Dom → Cod) (x₀ : Dom) (v : Cod) : Dom → Cod :=
  fun x => if x = x₀ then v else O x

theorem evalOracleComp_pin_untouched {Dom Cod α : Type} [DecidableEq Dom]
    (O : Dom → Cod) (x₀ : Dom) (v : Cod) :
    ∀ (prog : OracleComp Dom Cod α), x₀ ∉ queryLog O prog →
      evalOracleComp (pinOracle O x₀ v) prog = evalOracleComp O prog ∧
      queryLog (pinOracle O x₀ v) prog = queryLog O prog
  | .pure _, _ => ⟨rfl, rfl⟩
  | .query q next, hNotMem => by
    simp only [queryLog, List.mem_cons, not_or] at hNotMem
    have hqNe : q ≠ x₀ := fun hEq => hNotMem.1 hEq.symm
    have hPinQ : pinOracle O x₀ v q = O q := by simp [pinOracle, hqNe]
    simp only [evalOracleComp, queryLog, hPinQ]
    obtain ⟨hEval, hLog⟩ := evalOracleComp_pin_untouched O x₀ v (next (O q)) hNotMem.2
    exact ⟨hEval, congrArg (q :: ·) hLog⟩

/-- **Slice Reprogramming Lemma (`condProb_pin_untouched`)**. -/
theorem condProb_pin_untouched {Dom Cod α : Type} [DecidableEq Dom]
    (C : Nat) (decodeCod : Fin C → Cod)
    (O : Dom → Cod) (x₀ : Dom) (prog : OracleComp Dom Cod α) (accept : α → Bool)
    (guessProg : OracleComp Dom Cod (Fin C))
    (hUntouched : x₀ ∉ queryLog O prog)
    (hUntouchedGuess : x₀ ∉ queryLog O guessProg) :
    finSum C (fun c => if accept (evalOracleComp (pinOracle O x₀ (decodeCod c)) prog) then 1 else 0) =
      C * (if accept (evalOracleComp O prog) then 1 else 0) ∧
    finSum C (fun c => if evalOracleComp (pinOracle O x₀ (decodeCod c)) guessProg = c then 1 else 0) ≤
      (if 0 < C then 1 else 0) := by
  refine ⟨?_, ?_⟩
  · have hCongr :
        finSum C (fun c => if accept (evalOracleComp (pinOracle O x₀ (decodeCod c)) prog) then 1 else 0) =
        finSum C (fun _ => if accept (evalOracleComp O prog) then 1 else 0) := by
      apply finSum_congr
      intro c
      rw [(evalOracleComp_pin_untouched O x₀ (decodeCod c) prog hUntouched).1]
    rw [hCongr, finSum_const]
  · cases C with
    | zero => simp [finSum]
    | succ n =>
      have hCongr :
          finSum (n + 1) (fun c => if evalOracleComp (pinOracle O x₀ (decodeCod c)) guessProg = c then 1 else 0) =
          finSum (n + 1) (fun c => if c = evalOracleComp O guessProg then 1 else 0) := by
        apply finSum_congr
        intro c
        rw [(evalOracleComp_pin_untouched O x₀ (decodeCod c) guessProg hUntouchedGuess).1]
        by_cases hcg : evalOracleComp O guessProg = c
        · rw [hcg]
        · have hgc : c ≠ evalOracleComp O guessProg := fun h => hcg h.symm
          rw [ite_eq_right_iff.mpr (fun h => False.elim (hcg h)),
              ite_eq_right_iff.mpr (fun h => False.elim (hgc h))]
      rw [hCongr, finSum_eq_indicator]
      simp

abbrev UnifiedTreeDom (LeafBlock Digest32 : Type) := Sum LeafBlock (Digest32 × Digest32)

def merkleWalkQueries (depth : Nat) : Nat := 2 + 2 * depth

def stepCollisionHits (C : Nat) (prevDigests : List (Fin C)) : Nat :=
  finSum C (fun y => if y ∈ prevDigests then 1 else 0)

def cumulativeBirthdayBound : Nat → Nat
  | 0 => 1
  | q + 1 => cumulativeBirthdayBound q + q

theorem cumulativeBirthdayBound_le_sq_succ : ∀ (Q : Nat),
    cumulativeBirthdayBound Q ≤ Q * Q + 1
  | 0 => by simp [cumulativeBirthdayBound]
  | q + 1 => by
    simp only [cumulativeBirthdayBound]
    have ih := cumulativeBirthdayBound_le_sq_succ q
    have hExpand : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    omega

private theorem finSum_stepHits_le_sq_succ (C : Nat) :
    ∀ (Q : Nat) (stepHistory : (i : Nat) → i < Q → List (Fin C)),
      (∀ i (hi : i < Q), (stepHistory i hi).length ≤ i) →
      1 + finSum Q (fun idx => stepCollisionHits C (stepHistory idx.val idx.isLt)) ≤ Q * Q + 1
  | 0, _, _ => by simp [finSum]
  | q + 1, stepHistory, hHistLen => by
    have hPt : ∀ idx : Fin (q + 1),
        stepCollisionHits C (stepHistory idx.val idx.isLt) ≤ q := fun idx =>
      Nat.le_trans (Nat.le_trans (finSum_mem_list_le C _) (hHistLen idx.val idx.isLt))
        (Nat.le_of_lt_succ idx.isLt)
    have hSumLe : finSum (q + 1) (fun idx => stepCollisionHits C (stepHistory idx.val idx.isLt)) ≤
        (q + 1) * q := by
      rw [← finSum_const (q + 1) q]
      exact finSum_le_finSum hPt
    have hMulLe : (q + 1) * q ≤ (q + 1) * (q + 1) := Nat.mul_le_mul_left (q + 1) (Nat.le_succ q)
    omega

/-- **Unified `LeafBlock ⊕ (Digest32 × Digest32)` Tree Birthday Floor (`unifiedTreeGame_birthday_le`)**. -/
theorem unifiedTreeGame_birthday_le {LeafBlock Digest32 : Type}
    (C Q depth : Nat) (hCPos : 0 < C) (hWalk : merkleWalkQueries depth ≤ Q)
    (stepHistory : (i : Nat) → i < Q → List (Fin C))
    (hHistLen : ∀ i (hi : i < Q), (stepHistory i hi).length ≤ i)
    (leafA : LeafBlock) (nodeB : Digest32 × Digest32) :
    (Sum.inl leafA : UnifiedTreeDom LeafBlock Digest32) ≠ Sum.inr nodeB ∧
    ratLe (1 + finSum Q (fun idx => stepCollisionHits C (stepHistory idx.val idx.isLt)), C)
          (Q * Q + 1, C) ∧
    cumulativeBirthdayBound (merkleWalkQueries depth) ≤ Q * Q + 1 := by
  have hCumMono : ∀ a b, a ≤ b → cumulativeBirthdayBound a ≤ cumulativeBirthdayBound b := by
    intro a b hab
    induction hab with
    | refl => exact Nat.le_refl _
    | step _ ih => simp only [cumulativeBirthdayBound]; omega
  refine ⟨?_, ?_, Nat.le_trans (hCumMono _ _ hWalk) (cumulativeBirthdayBound_le_sq_succ Q)⟩
  · intro h; cases h
  · unfold ratLe
    exact ⟨hCPos, hCPos, Nat.mul_le_mul_right C (finSum_stepHits_le_sq_succ C Q stepHistory hHistLen)⟩

def keyedPrfRealAccept {TagDom Cod : Type} (cardB : Nat)
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool) : Nat :=
  finSum cardB (fun kStar =>
    let world0 : Fin cardB × TagDom → Cod :=
      fun q => if q.1 = kStar then secretFn q.2 else baseO q
    if evalOracleComp world0 A then 1 else 0)

def keyedPrfIdealAccept {TagDom Cod : Type} (cardB : Nat)
    (baseO : Fin cardB × TagDom → Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool) : Nat :=
  finSum cardB (fun _ => if evalOracleComp baseO A then 1 else 0)

theorem evalOracleComp_agree_if_key_unqueried {TagDom Cod α : Type} {cardB : Nat}
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod) (kStar : Fin cardB) :
    ∀ (prog : OracleComp (Fin cardB × TagDom) Cod α),
      kStar ∉ (queryLog baseO prog).map Prod.fst →
      evalOracleComp (fun q => if q.1 = kStar then secretFn q.2 else baseO q) prog =
        evalOracleComp baseO prog
  | .pure _, _ => rfl
  | .query q next, hNotMem => by
    simp only [queryLog, List.map_cons, List.mem_cons, not_or] at hNotMem
    have hNe : q.1 ≠ kStar := fun h => hNotMem.1 h.symm
    simp only [evalOracleComp, hNe, ↓reduceIte]
    exact evalOracleComp_agree_if_key_unqueried baseO secretFn kStar (next (baseO q)) hNotMem.2

/-- **Keyed-ROM Blinding / PRF Hiding Floor (`hidingAdv_le`)**. -/
theorem hidingAdv_le {TagDom Cod : Type}
    (cardB Q : Nat) (hCardPos : 0 < cardB)
    (baseO : Fin cardB × TagDom → Cod) (secretFn : TagDom → Cod)
    (A : OracleComp (Fin cardB × TagDom) Cod Bool)
    (hBounded : QueryBounded Q A) :
    let advNum := natAbsDiff (keyedPrfRealAccept cardB baseO secretFn A)
                             (keyedPrfIdealAccept cardB baseO A)
    advNum ≤ Q ∧
    ratLe (advNum, cardB) (2 * Q, cardB) := by
  intro advNum
  let touchedKeys : List (Fin cardB) := (queryLog baseO A).map Prod.fst
  have hLen : touchedKeys.length ≤ Q := by
    simp only [touchedKeys, List.length_map]
    exact queryLog_length_le baseO hBounded
  have hDiff : advNum ≤ finSum cardB (fun k => if k ∈ touchedKeys then 1 else 0) := by
    have hBadEq :
        finSum cardB (fun k => if decide (k ∈ touchedKeys) = true then 1 else 0) =
        finSum cardB (fun k => if k ∈ touchedKeys then 1 else 0) := by
      apply finSum_congr
      intro k
      by_cases hk : k ∈ touchedKeys <;> simp [hk]
    rw [← hBadEq]
    exact finSum_indicator_diff_le
      (fun kStar => evalOracleComp (fun q => if q.1 = kStar then secretFn q.2 else baseO q) A)
      (fun _ => evalOracleComp baseO A)
      (fun k => decide (k ∈ touchedKeys))
      (fun k hkFalse => by
        have hkNotMem : k ∉ touchedKeys := fun hm => by simp [hm] at hkFalse
        exact evalOracleComp_agree_if_key_unqueried baseO secretFn k A hkNotMem)
  have hAdvLeQ : advNum ≤ Q :=
    Nat.le_trans hDiff (Nat.le_trans (finSum_mem_list_le cardB touchedKeys) hLen)
  refine ⟨hAdvLeQ, ?_⟩
  unfold ratLe
  have h2Q : advNum ≤ 2 * Q := by omega
  exact ⟨hCardPos, hCardPos, Nat.mul_le_mul_right cardB h2Q⟩

theorem hidingAdv_le_deployed {TagDom Cod : Type} (Q : Nat)
    (baseBv : Fin deployedCardBitVec256 × TagDom → Cod)
    (baseGl : Fin deployedCardGoldilocks4 × TagDom → Cod)
    (secFn : TagDom → Cod)
    (Abv : OracleComp (Fin deployedCardBitVec256 × TagDom) Cod Bool)
    (Agl : OracleComp (Fin deployedCardGoldilocks4 × TagDom) Cod Bool)
    (hBv : QueryBounded Q Abv) (hGl : QueryBounded Q Agl) :
    ratLe (natAbsDiff (keyedPrfRealAccept deployedCardBitVec256 baseBv secFn Abv)
                      (keyedPrfIdealAccept deployedCardBitVec256 baseBv Abv),
           deployedCardBitVec256)
          (2 * Q, deployedCardBitVec256) ∧
    ratLe (natAbsDiff (keyedPrfRealAccept deployedCardGoldilocks4 baseGl secFn Agl)
                      (keyedPrfIdealAccept deployedCardGoldilocks4 baseGl Agl),
           deployedCardGoldilocks4)
          (2 * Q, deployedCardGoldilocks4) :=
  ⟨(hidingAdv_le deployedCardBitVec256 Q (by unfold deployedCardBitVec256; decide) baseBv secFn Abv hBv).2,
   (hidingAdv_le deployedCardGoldilocks4 Q (by unfold deployedCardGoldilocks4; decide) baseGl secFn Agl hGl).2⟩

def buildFullTableReader (cardB : Nat) : (rem : Nat) → rem ≤ cardB →
    OracleComp (Fin cardB × Unit) Bool Bool
  | 0, _ => .pure false
  | m + 1, hm =>
    .query (⟨cardB - (m + 1), by omega⟩, ()) (fun b =>
      if b then .pure true else buildFullTableReader cardB m (by omega))

def oneQueryGuesser (cardB : Nat) (hPos : 0 < cardB) : OracleComp (Fin cardB × Unit) Bool Bool :=
  .query (⟨0, hPos⟩, ()) (fun b => .pure b)

def zeroQueryHardcoder (cardB : Nat) (c : Bool) : OracleComp (Fin cardB × Unit) Bool Bool :=
  .pure c

theorem lazyRo_query_regime_characterization (cardB : Nat) (hPos : 0 < cardB) (c : Bool) :
    natAbsDiff (keyedPrfRealAccept cardB (fun _ => false) (fun _ => true) (zeroQueryHardcoder cardB c))
               (keyedPrfIdealAccept cardB (fun _ => false) (zeroQueryHardcoder cardB c)) = 0 ∧
    (0 < natAbsDiff (keyedPrfRealAccept cardB (fun _ => false) (fun _ => true) (oneQueryGuesser cardB hPos))
                    (keyedPrfIdealAccept cardB (fun _ => false) (oneQueryGuesser cardB hPos)) ∧
     QueryBounded 1 (oneQueryGuesser cardB hPos)) ∧
    2 * 1 < natAbsDiff (keyedPrfRealAccept 8 (fun _ => false) (fun _ => true) (buildFullTableReader 8 8 (Nat.le_refl 8)))
                       (keyedPrfIdealAccept 8 (fun _ => false) (buildFullTableReader 8 8 (Nat.le_refl 8))) := by
  refine ⟨?_, ⟨?_, fun _ => trivial⟩, by decide⟩
  · unfold keyedPrfRealAccept keyedPrfIdealAccept zeroQueryHardcoder evalOracleComp
    simp [natAbsDiff]
  · unfold keyedPrfRealAccept keyedPrfIdealAccept oneQueryGuesser evalOracleComp
    have hIdeal0 : finSum cardB (fun _ => (0 : Nat)) = 0 := by rw [finSum_const]; omega
    have hReal1 :
        finSum cardB (fun kStar : Fin cardB =>
          if (if (⟨0, hPos⟩ : Fin cardB) = kStar then true else false) = true then 1 else 0) = 1 := by
      have hCongr :
          finSum cardB (fun kStar : Fin cardB =>
            if (if (⟨0, hPos⟩ : Fin cardB) = kStar then true else false) = true then 1 else 0) =
          finSum cardB (fun kStar : Fin cardB => if kStar = ⟨0, hPos⟩ then 1 else 0) := by
        apply finSum_congr
        intro kStar
        by_cases hk : kStar = ⟨0, hPos⟩
        · subst hk; simp
        · have hne : (⟨0, hPos⟩ : Fin cardB) ≠ kStar := fun h => hk h.symm
          simp [hk, hne]
      rw [hCongr, finSum_eq_indicator]
    change 0 < natAbsDiff
      (finSum cardB (fun kStar : Fin cardB =>
        if (if (⟨0, hPos⟩ : Fin cardB) = kStar then true else false) = true then 1 else 0))
      (finSum cardB (fun _ => 0))
    rw [hReal1, hIdeal0]
    decide

/-! ## 2. Polymorphic Shamir Pad-Space Bijection (`Goldilocks`, `GoldilocksExt2`, `TowerElem k`) -/

section PolymorphicPadBijection
open CommRingOps

def polyAddFixed {R : Type} [CommRingOps R] : List R → List R → List R
  | a :: as, b :: bs => add a b :: polyAddFixed as bs
  | [], _ => []
  | _, [] => []

def polySubFixed {R : Type} [CommRingOps R] : List R → List R → List R
  | a :: as, b :: bs => sub a b :: polySubFixed as bs
  | [], _ => []
  | _, [] => []

def polyScale {R : Type} [CommRingOps R] (s : R) : List R → List R
  | [] => []
  | c :: cs => mul s c :: polyScale s cs

theorem polyAddFixed_length {R : Type} [CommRingOps R] :
    ∀ (p q : List R), p.length = q.length → (polyAddFixed p q).length = p.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polyAddFixed, polyAddFixed_length as bs h]

theorem polySubFixed_length {R : Type} [CommRingOps R] :
    ∀ (p q : List R), p.length = q.length → (polySubFixed p q).length = p.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polySubFixed, polySubFixed_length as bs h]

theorem polyScale_length {R : Type} [CommRingOps R] (s : R) (p : List R) :
    (polyScale s p).length = p.length := by
  induction p <;> simp [polyScale, *]

private theorem add_sub_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    sub (add a b) b = a := by
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
      LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

private theorem sub_add_cancel_right {R : Type} [LawfulCommRing R] (a b : R) :
    add (sub a b) b = a := by
  rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

theorem polySub_polyAdd_cancel {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R), p.length = q.length → polySubFixed (polyAddFixed p q) q = p
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polyAddFixed, polySubFixed, add_sub_cancel_right, polySub_polyAdd_cancel as bs h]

theorem polyAdd_polySub_cancel {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R), p.length = q.length → polyAddFixed (polySubFixed p q) q = p
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [polyAddFixed, polySubFixed, sub_add_cancel_right, polyAdd_polySub_cancel as bs h]

theorem evalCoeffs_addFixed {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R) (x : R), p.length = q.length →
      RoundPoly.evalCoeffs (polyAddFixed p q) x =
        add (RoundPoly.evalCoeffs p x) (RoundPoly.evalCoeffs q x)
  | [], [], _, _ => by simp [polyAddFixed, LawfulCommRing.add_zero]
  | a :: as, b :: bs, x, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [polyAddFixed, RoundPoly.evalCoeffs_cons, evalCoeffs_addFixed as bs x h]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem evalCoeffs_subFixed {R : Type} [LawfulCommRing R] :
    ∀ (p q : List R) (x : R), p.length = q.length →
      RoundPoly.evalCoeffs (polySubFixed p q) x =
        sub (RoundPoly.evalCoeffs p x) (RoundPoly.evalCoeffs q x)
  | [], [], _, _ => by simp [polySubFixed, LawfulCommRing.sub_self]
  | a :: as, b :: bs, x, h => by
    have hLen : (polySubFixed (a :: as) (b :: bs)).length = (b :: bs).length := by
      rw [polySubFixed_length (a :: as) (b :: bs) h, h]
    have hEq := evalCoeffs_addFixed (polySubFixed (a :: as) (b :: bs)) (b :: bs) x hLen
    rw [polyAdd_polySub_cancel (a :: as) (b :: bs) h] at hEq
    have hSub := congrArg (fun u => sub u (RoundPoly.evalCoeffs (b :: bs) x)) hEq
    rw [add_sub_cancel_right] at hSub
    exact hSub.symm

theorem evalCoeffs_scale {R : Type} [LawfulCommRing R] (s : R) :
    ∀ (p : List R) (x : R),
      RoundPoly.evalCoeffs (polyScale s p) x = mul s (RoundPoly.evalCoeffs p x)
  | [], _ => by simp [polyScale, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    simp only [polyScale, RoundPoly.evalCoeffs_cons, evalCoeffs_scale s cs x]
    rw [LawfulCommRing.left_distrib, ← LawfulCommRing.mul_assoc x s _,
        LawfulCommRing.mul_comm x s, LawfulCommRing.mul_assoc s x _]

private def mulLinearAux {R : Type} [CommRingOps R] (k prev : R) : List R → List R
  | [] => [prev]
  | c :: cs => add c prev :: mulLinearAux k (mul k c) cs

def mulOnePlusKX {R : Type} [CommRingOps R] (k : R) : List R → List R
  | [] => []
  | c :: cs => c :: mulLinearAux k (mul k c) cs

private theorem mulLinearAux_length {R : Type} [CommRingOps R] (k prev : R) :
    ∀ (cs : List R), (mulLinearAux k prev cs).length = cs.length + 1
  | [] => rfl
  | _ :: cs => by simp [mulLinearAux, mulLinearAux_length k _ cs]

theorem mulOnePlusKX_length {R : Type} [CommRingOps R] (k : R) :
    ∀ (p : List R), p ≠ [] → (mulOnePlusKX k p).length = p.length + 1
  | [], h => False.elim (h rfl)
  | _ :: _, _ => by simp [mulOnePlusKX, mulLinearAux_length]

private theorem evalCoeffs_mulLinearAux {R : Type} [LawfulCommRing R] (k prev : R) :
    ∀ (cs : List R) (x : R),
      RoundPoly.evalCoeffs (mulLinearAux k prev cs) x =
        add prev (mul (add one (mul k x)) (RoundPoly.evalCoeffs cs x))
  | [], _ => by
    simp [mulLinearAux, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | c :: cs, x => by
    simp only [mulLinearAux, RoundPoly.evalCoeffs_cons, evalCoeffs_mulLinearAux k (mul k c) cs x]
    rw [LawfulCommRing.left_distrib x, LawfulCommRing.left_distrib (add one (mul k x)),
        LawfulCommRing.right_distrib one (mul k x) c, LawfulCommRing.one_mul]
    have hxc : mul x (mul k c) = mul (mul k x) c := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x k]
    have hxs : mul x (mul (add one (mul k x)) (RoundPoly.evalCoeffs cs x)) =
        mul (add one (mul k x)) (mul x (RoundPoly.evalCoeffs cs x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x (add one (mul k x)),
          LawfulCommRing.mul_assoc]
    rw [hxc, hxs, LawfulCommRing.add_comm c prev, LawfulCommRing.add_assoc prev c,
        LawfulCommRing.add_assoc c (mul (mul k x) c)]

theorem evalCoeffs_mulOnePlusKX {R : Type} [LawfulCommRing R] (k : R) :
    ∀ (p : List R) (x : R),
      RoundPoly.evalCoeffs (mulOnePlusKX k p) x =
        mul (add one (mul k x)) (RoundPoly.evalCoeffs p x)
  | [], _ => by simp [mulOnePlusKX, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    simp only [mulOnePlusKX, RoundPoly.evalCoeffs_cons, evalCoeffs_mulLinearAux]
    rw [LawfulCommRing.left_distrib x, LawfulCommRing.left_distrib (add one (mul k x)),
        LawfulCommRing.right_distrib one (mul k x) c, LawfulCommRing.one_mul, ← LawfulCommRing.add_assoc]
    have hxc : mul x (mul k c) = mul (mul k x) c := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x k]
    have hxs : mul x (mul (add one (mul k x)) (RoundPoly.evalCoeffs cs x)) =
        mul (add one (mul k x)) (mul x (RoundPoly.evalCoeffs cs x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm x (add one (mul k x)),
          LawfulCommRing.mul_assoc]
    rw [hxc, hxs]

def vanishCorruptRaw {R : Type} [CommRingOps R] (inv : R → R) : List R → List R
  | [] => [one]
  | xc :: rest => mulOnePlusKX (neg (inv xc)) (vanishCorruptRaw inv rest)

theorem vanishCorruptRaw_nonempty {R : Type} [CommRingOps R] (inv : R → R) :
    ∀ (cs : List R), vanishCorruptRaw inv cs ≠ []
  | [] => by simp [vanishCorruptRaw]
  | _ :: rest => by
    have ih := vanishCorruptRaw_nonempty inv rest
    cases h : vanishCorruptRaw inv rest with
    | nil => exact False.elim (ih h)
    | cons c cs => simp [vanishCorruptRaw, h, mulOnePlusKX]

theorem vanishCorruptRaw_length {R : Type} [CommRingOps R] (inv : R → R) :
    ∀ (cs : List R), (vanishCorruptRaw inv cs).length = cs.length + 1
  | [] => rfl
  | _ :: rest => by
    simp only [vanishCorruptRaw, List.length_cons]
    rw [mulOnePlusKX_length _ _ (vanishCorruptRaw_nonempty inv rest), vanishCorruptRaw_length inv rest]

theorem evalCoeffs_replicate_zero {R : Type} [LawfulCommRing R] :
    ∀ (k : Nat) (x : R), RoundPoly.evalCoeffs (List.replicate k (zero : R)) x = zero
  | 0, _ => rfl
  | k + 1, x => by
    simp [List.replicate_succ, evalCoeffs_replicate_zero k x,
          LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

theorem evalCoeffs_padZerosRight {R : Type} [LawfulCommRing R] :
    ∀ (p : List R) (k : Nat) (x : R),
      RoundPoly.evalCoeffs (p ++ List.replicate k (zero : R)) x = RoundPoly.evalCoeffs p x
  | [], _, _ => by simp [evalCoeffs_replicate_zero]
  | _ :: cs, k, x => by simp [List.cons_append, evalCoeffs_padZerosRight cs k x]

def vanishCorruptUnit0 {R : Type} [CommRingOps R] (inv : R → R) (t : Nat) (corruptPts : List R) : List R :=
  let raw := vanishCorruptRaw inv corruptPts
  raw ++ List.replicate (t - raw.length) zero

theorem vanishCorruptUnit0_props {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    {t : Nat} {corruptPts : List R}
    (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero) :
    (vanishCorruptUnit0 inv t corruptPts).length = t ∧
    RoundPoly.evalCoeffs (vanishCorruptUnit0 inv t corruptPts) zero = one ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs (vanishCorruptUnit0 inv t corruptPts) xc = zero) := by
  have hRawLen := vanishCorruptRaw_length inv corruptPts
  have hAtZero : ∀ cs : List R, RoundPoly.evalCoeffs (vanishCorruptRaw inv cs) zero = one := by
    intro cs
    induction cs with
    | nil =>
      simp [vanishCorruptRaw, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | cons xc rest ih =>
      simp [vanishCorruptRaw, evalCoeffs_mulOnePlusKX, ih,
            LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.mul_one]
  have hAtCorr : ∀ {cs : List R} {x : R},
      (∀ c ∈ cs, c ≠ zero) → x ∈ cs → RoundPoly.evalCoeffs (vanishCorruptRaw inv cs) x = zero := by
    intro cs x hNz hx
    induction cs with
    | nil => cases hx
    | cons xc rest ih =>
      simp only [vanishCorruptRaw, evalCoeffs_mulOnePlusKX]
      rcases List.mem_cons.mp hx with rfl | hMemRest
      · have hxNz : x ≠ zero := hNz x (.head rest)
        have hFactor : add one (mul (neg (inv x)) x) = zero := by
          rw [LawfulCommRing.neg_mul, LawfulCommRing.mul_comm (inv x) x,
              hInv x hxNz, LawfulCommRing.add_right_neg]
        rw [hFactor, LawfulCommRing.zero_mul]
      · rw [ih (fun c hc => hNz c (.tail xc hc)) hMemRest, LawfulCommRing.mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · unfold vanishCorruptUnit0
    dsimp only
    rw [List.length_append, List.length_replicate, hRawLen]
    omega
  · unfold vanishCorruptUnit0
    dsimp only
    rw [evalCoeffs_padZerosRight, hAtZero]
  · intro xc hxc
    unfold vanishCorruptUnit0
    dsimp only
    rw [evalCoeffs_padZerosRight]
    exact hAtCorr hNonZero hxc

structure SimpleEquiv (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b

abbrev ShamirPadPoly (R : Type) (t : Nat) := { p : List R // p.length = t }

/-- **Constructive Polymorphic Shamir Pad-Space Bijection (`shamir_rebalanceEquiv`)**. -/
@[expose] def shamir_rebalanceEquiv {R : Type} [LawfulCommRing R]
    (inv : R → R) (t : Nat) (corruptPts : List R)
    (w : R) (hCard : corruptPts.length + 1 ≤ t) :
    SimpleEquiv (ShamirPadPoly R t) (ShamirPadPoly R t) :=
  let delta := polyScale w (vanishCorruptUnit0 inv t corruptPts)
  have hDeltaLen : delta.length = t := by
    rw [polyScale_length]
    unfold vanishCorruptUnit0; dsimp only
    rw [List.length_append, List.length_replicate, vanishCorruptRaw_length]
    omega
  { toFun := fun ⟨p, hp⟩ => ⟨polyAddFixed p delta, by rw [polyAddFixed_length p delta (hp.trans hDeltaLen.symm), hp]⟩
    invFun := fun ⟨q, hq⟩ => ⟨polySubFixed q delta, by rw [polySubFixed_length q delta (hq.trans hDeltaLen.symm), hq]⟩
    left_inv := fun ⟨p, hp⟩ => Subtype.ext (polySub_polyAdd_cancel p delta (hp.trans hDeltaLen.symm))
    right_inv := fun ⟨q, hq⟩ => Subtype.ext (polyAdd_polySub_cancel q delta (hq.trans hDeltaLen.symm)) }

theorem shamir_tower_rebalance_involutive (k t : Nat)
    (corruptPts : List (TowerElem k)) (w : TowerElem k)
    (hCard : corruptPts.length + 1 ≤ t)
    (P : ShamirPadPoly (TowerElem k) t) :
    let eqv := shamir_rebalanceEquiv (towerInv k) t corruptPts w hCard
    eqv.toFun (eqv.toFun P) = P := by
  intro eqv
  have hAddEqSub : ∀ (u v : List (TowerElem k)), polyAddFixed u v = polySubFixed u v := by
    intro u v
    induction u generalizing v with
    | nil => cases v <;> rfl
    | cons a as ih =>
      cases v with
      | nil => rfl
      | cons b bs =>
        simp only [polyAddFixed, polySubFixed]
        exact congrArg (towerAdd k a b :: ·) (ih bs)
  have hEqInv : eqv.toFun (eqv.toFun P) = eqv.invFun (eqv.toFun P) := by
    apply Subtype.ext
    exact hAddEqSub _ _
  rw [hEqInv, eqv.left_inv]

/-- **Pad-Space Bijection Uniformity & Zero-Knowledge Theorem (`pad_bijection_masked_openings_uniform`)**. -/
theorem pad_bijection_masked_openings_uniform {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (t : Nat) (corruptPts : List R)
    (w : R) (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero)
    (P : ShamirPadPoly R t) :
    let Q := (shamir_rebalanceEquiv inv t corruptPts w hCard).toFun P
    add zero (RoundPoly.evalCoeffs Q.1 zero) =
      add w (RoundPoly.evalCoeffs P.1 zero) ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs Q.1 xc = RoundPoly.evalCoeffs P.1 xc) := by
  intro Q
  obtain ⟨hULen, hU0, hUCorr⟩ := vanishCorruptUnit0_props inv hInv hCard hNonZero
  have hScaleLen : (polyScale w (vanishCorruptUnit0 inv t corruptPts)).length = t := by
    rw [polyScale_length, hULen]
  refine ⟨?_, ?_⟩
  · change add zero
      (RoundPoly.evalCoeffs (polyAddFixed P.1 (polyScale w (vanishCorruptUnit0 inv t corruptPts))) zero) = _
    rw [evalCoeffs_addFixed P.1 _ _ (P.2.trans hScaleLen.symm), evalCoeffs_scale, hU0,
        LawfulCommRing.zero_add, LawfulCommRing.mul_one, LawfulCommRing.add_comm]
  · intro xc hxc
    change RoundPoly.evalCoeffs (polyAddFixed P.1 (polyScale w (vanishCorruptUnit0 inv t corruptPts))) xc = _
    rw [evalCoeffs_addFixed P.1 _ _ (P.2.trans hScaleLen.symm), evalCoeffs_scale, hUCorr xc hxc,
        LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

theorem pad_bijection_goldilocks_and_tower (k t : Nat)
    (corrGl : List Goldilocks) (wGl : Goldilocks)
    (hCardGl : corrGl.length + 1 ≤ t) (hNzGl : ∀ c ∈ corrGl, c ≠ CommRingOps.zero)
    (PGl : ShamirPadPoly Goldilocks t)
    (corrTw : List (TowerElem k)) (wTw : TowerElem k)
    (hCardTw : corrTw.length + 1 ≤ t) (hNzTw : ∀ c ∈ corrTw, c ≠ CommRingOps.zero)
    (PTw : ShamirPadPoly (TowerElem k) t) :
    let QGl := (shamir_rebalanceEquiv Goldilocks.inv t corrGl wGl hCardGl).toFun PGl
    let QTw := (shamir_rebalanceEquiv (towerInv k) t corrTw wTw hCardTw).toFun PTw
    (add zero (RoundPoly.evalCoeffs QGl.1 zero) = add wGl (RoundPoly.evalCoeffs PGl.1 zero) ∧
     ∀ xc ∈ corrGl, RoundPoly.evalCoeffs QGl.1 xc = RoundPoly.evalCoeffs PGl.1 xc) ∧
    (add zero (RoundPoly.evalCoeffs QTw.1 zero) = add wTw (RoundPoly.evalCoeffs PTw.1 zero) ∧
     ∀ xc ∈ corrTw, RoundPoly.evalCoeffs QTw.1 xc = RoundPoly.evalCoeffs PTw.1 xc) :=
  ⟨pad_bijection_masked_openings_uniform Goldilocks.inv (fun _ hx => Goldilocks.mul_inv_cancel hx) t corrGl wGl hCardGl hNzGl PGl,
   pad_bijection_masked_openings_uniform (towerInv k) (towerMul_inv k) t corrTw wTw hCardTw hNzTw PTw⟩

theorem full_collusion_breaks_hiding {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R]
    (t : Nat) (corruptPts : List R)
    (hFull : corruptPts.length = t) (hNodup : corruptPts.Nodup)
    (w₁ w₂ : R) (hDistinct : w₁ ≠ w₂)
    (P Q : ShamirPadPoly R t)
    (hSameShares : ∀ xc ∈ corruptPts, RoundPoly.evalCoeffs P.1 xc = RoundPoly.evalCoeffs Q.1 xc) :
    add w₁ (RoundPoly.evalCoeffs P.1 zero) ≠ add w₂ (RoundPoly.evalCoeffs Q.1 zero) := by
  have hZeroEq : RoundPoly.evalCoeffs P.1 zero = RoundPoly.evalCoeffs Q.1 zero := by
    cases t with
    | zero =>
      have hp0 : P.1 = [] := List.eq_nil_of_length_eq_zero P.2
      have hq0 : Q.1 = [] := List.eq_nil_of_length_eq_zero Q.2
      rw [hp0, hq0]
    | succ d =>
      let diff := polySubFixed P.1 Q.1
      have hDiffLen : diff.length ≤ d + 1 := by
        rw [polySubFixed_length P.1 Q.1 (P.2.trans Q.2.symm), P.2]
        exact Nat.le_refl (d + 1)
      if hAt0 : RoundPoly.evalCoeffs P.1 zero = RoundPoly.evalCoeffs Q.1 zero then
        exact hAt0
      else
        exfalso
        have hNz0 : RoundPoly.evalCoeffs diff zero ≠ zero := by
          rw [evalCoeffs_subFixed P.1 Q.1 zero (P.2.trans Q.2.symm)]
          intro hSub0
          have hAdd := congrArg (fun u => add u (RoundPoly.evalCoeffs Q.1 zero)) hSub0
          rw [sub_add_cancel_right, LawfulCommRing.zero_add] at hAdd
          exact hAt0 hAdd
        have hFiltEq : corruptPts.filter (fun r => decide (RoundPoly.evalCoeffs diff r = zero)) =
            corruptPts := by
          apply List.filter_eq_self.mpr
          intro xc hxc
          rw [evalCoeffs_subFixed P.1 Q.1 xc (P.2.trans Q.2.symm), hSameShares xc hxc,
              LawfulCommRing.sub_self]
          exact decide_eq_true rfl
        have hBound := RoundPoly.roots_nodup_length_le d diff corruptPts hNodup hDiffLen ⟨zero, hNz0⟩
        rw [hFiltEq, hFull] at hBound
        omega
  intro hEqOpen
  rw [hZeroEq] at hEqOpen
  have hSub := congrArg (fun u => sub u (RoundPoly.evalCoeffs Q.1 zero)) hEqOpen
  rw [add_sub_cancel_right, add_sub_cancel_right] at hSub
  exact hDistinct hSub

theorem unpadded_open_refutes_hiding {R : Type} [LawfulCommRing R]
    (w₁ w₂ : R) (hDistinct : w₁ ≠ w₂) :
    add w₁ zero ≠ add w₂ zero := by
  rw [LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  exact hDistinct

end PolymorphicPadBijection

/-! ## 3. Vandermonde-at-Zero Reconstruction & Canetti UC Signatures (`idealSig`) -/

@[expose] def ringDot {R : Type} [CommRingOps R] : List R → List R → R
  | l :: ls, y :: ys => CommRingOps.add (CommRingOps.mul l y) (ringDot ls ys)
  | _, _ => CommRingOps.zero

def ringPow {R : Type} [CommRingOps R] (x : R) : Nat → R
  | 0 => CommRingOps.one
  | k + 1 => CommRingOps.mul (ringPow x k) x

private def evalShifted {R : Type} [CommRingOps R] : List R → Nat → R → R
  | [], _, _ => CommRingOps.zero
  | c :: cs, shift, x => CommRingOps.add (CommRingOps.mul c (ringPow x shift)) (evalShifted cs (shift + 1) x)

private theorem evalShifted_eq_mul_pow {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (shift : Nat) (x : R),
      evalShifted cs shift x = CommRingOps.mul (ringPow x shift) (RoundPoly.evalCoeffs cs x)
  | [], shift, x => by simp [evalShifted, LawfulCommRing.mul_zero]
  | c :: cs, shift, x => by
    simp only [evalShifted, RoundPoly.evalCoeffs_cons, evalShifted_eq_mul_pow cs (shift + 1) x, ringPow]
    rw [LawfulCommRing.mul_comm c (ringPow x shift), LawfulCommRing.mul_assoc (ringPow x shift) x _,
        ← LawfulCommRing.left_distrib]

private theorem ringDot_map_zero {R : Type} [LawfulCommRing R] :
    ∀ (ls pts : List R), ringDot ls (pts.map (fun _ => CommRingOps.zero)) = CommRingOps.zero
  | [], _ => by simp [ringDot]
  | _ :: _, [] => by simp [ringDot]
  | _ :: ls, _ :: ps => by
    simp only [List.map_cons, ringDot, LawfulCommRing.mul_zero, ringDot_map_zero ls ps, LawfulCommRing.zero_add]

private theorem ringDot_map_add {R : Type} [LawfulCommRing R] (f g : R → R) :
    ∀ (ls pts : List R),
      ringDot ls (pts.map (fun x => CommRingOps.add (f x) (g x))) =
        CommRingOps.add (ringDot ls (pts.map f)) (ringDot ls (pts.map g))
  | [], _ => by simp [ringDot, LawfulCommRing.add_zero]
  | _, [] => by simp [ringDot, LawfulCommRing.add_zero]
  | _ :: ls, _ :: ps => by
    simp only [List.map_cons, ringDot, ringDot_map_add f g ls ps,
               LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

private theorem ringDot_map_scale {R : Type} [LawfulCommRing R] (c : R) (f : R → R) :
    ∀ (ls pts : List R),
      ringDot ls (pts.map (fun x => CommRingOps.mul c (f x))) =
        CommRingOps.mul c (ringDot ls (pts.map f))
  | [], _ => by simp [ringDot, LawfulCommRing.mul_zero]
  | _, [] => by simp [ringDot, LawfulCommRing.mul_zero]
  | l :: ls, p :: ps => by
    simp only [List.map_cons, ringDot, ringDot_map_scale c f ls ps]
    have hSwap : CommRingOps.mul l (CommRingOps.mul c (f p)) = CommRingOps.mul c (CommRingOps.mul l (f p)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm l c, LawfulCommRing.mul_assoc]
    rw [hSwap, ← LawfulCommRing.left_distrib]

private theorem ringDot_evalShifted_tail_zero {R : Type} [LawfulCommRing R]
    (lambdas pts : List R) (t : Nat)
    (hHigher : ∀ d, 1 ≤ d → d < t → ringDot lambdas (pts.map (fun x => ringPow x d)) = CommRingOps.zero) :
    ∀ (cs : List R) (shift : Nat),
      1 ≤ shift → shift + cs.length ≤ t →
      ringDot lambdas (pts.map (fun x => evalShifted cs shift x)) = CommRingOps.zero
  | [], _, _, _ => ringDot_map_zero lambdas pts
  | _ :: cs, shift, hGe1, hBound => by
    simp only [List.length_cons] at hBound
    simp only [evalShifted]
    rw [ringDot_map_add, ringDot_map_scale, hHigher shift hGe1 (by omega),
        LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
    exact ringDot_evalShifted_tail_zero lambdas pts t hHigher cs (shift + 1) (by omega) (by omega)

/-- **Polymorphic Vandermonde / Lagrange-at-Zero Reconstruction (`lagrangeAtZero_evalCoeffs`)**. -/
theorem lagrangeAtZero_evalCoeffs {R : Type} [LawfulCommRing R]
    (lambdas pts coeffs : List R) (t : Nat)
    (hLen : coeffs.length ≤ t)
    (hZero : ringDot lambdas (pts.map (fun _ => CommRingOps.one)) = CommRingOps.one)
    (hHigher : ∀ d, 1 ≤ d → d < t → ringDot lambdas (pts.map (fun x => ringPow x d)) = CommRingOps.zero) :
    ringDot lambdas (pts.map (fun x => RoundPoly.evalCoeffs coeffs x)) =
      RoundPoly.evalCoeffs coeffs CommRingOps.zero := by
  have hToShift : ∀ x : R, RoundPoly.evalCoeffs coeffs x = evalShifted coeffs 0 x := by
    intro x
    rw [evalShifted_eq_mul_pow coeffs 0 x, ringPow, LawfulCommRing.one_mul]
  have hMapEq : pts.map (fun x => RoundPoly.evalCoeffs coeffs x) =
      pts.map (fun x => evalShifted coeffs 0 x) := List.map_congr_left (fun x _ => hToShift x)
  rw [hMapEq]
  cases coeffs with
  | nil => exact ringDot_map_zero lambdas pts
  | cons c0 rest =>
    simp only [List.length_cons] at hLen
    simp only [evalShifted, ringPow, RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [ringDot_map_add, ringDot_map_scale, hZero, LawfulCommRing.mul_one,
        ringDot_evalShifted_tail_zero lambdas pts t hHigher rest 1 (by omega) (by omega),
        LawfulCommRing.add_zero]

structure AbstractSigScheme (PK SK Msg Sig : Type) where
  sign : SK → Msg → Sig
  verify : PK → Msg → Sig → Bool
  complete : PK → SK → Prop
  completeness : ∀ {pk sk}, complete pk sk → ∀ m, verify pk m (sign sk m) = true

inductive UcSigEnv (PK Msg Sig : Type) where
  | halt (verdict : Bool)
  | stepSign (m : Msg) (next : Sig → UcSigEnv PK Msg Sig)
  | stepVerify (m : Msg) (sig : Sig) (next : Bool → UcSigEnv PK Msg Sig)

def execRealSig {PK SK Msg Sig : Type}
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) :
    UcSigEnv PK Msg Sig → Bool
  | .halt b => b
  | .stepSign m next => execRealSig S pk sk (next (S.sign sk m))
  | .stepVerify m sig next => execRealSig S pk sk (next (S.verify pk m sig))

@[expose] def idealSigVerify {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK)
    (recorded : List Msg) (m : Msg) (sig : Sig) : Bool :=
  decide (m ∈ recorded) && S.verify pk m sig

theorem idealSig_unforgeable {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK)
    (recorded : List Msg) (m : Msg) (sig : Sig) (hFresh : m ∉ recorded) :
    idealSigVerify S pk recorded m sig = false := by
  simp [idealSigVerify, hFresh]

/-- **Canetti Ideal Signature Execution (`execIdealSig`) — Strictly `sk`-Free (`[P0-11]`)**.
`F_SIG` stores only `(pk, recorded)` and invokes the ideal-world simulator's public string callback
`simSign : Msg → Sig`; `sk : SK` does NOT appear anywhere in `execIdealSig`, `findEnvForgery`,
or `signedBeforeForgery`! -/
def execIdealSig {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (simSign : Msg → Sig)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → Bool
  | .halt b => b
  | .stepSign m next => execIdealSig S pk simSign (m :: recorded) (next (simSign m))
  | .stepVerify m sig next =>
    execIdealSig S pk simSign recorded (next (idealSigVerify S pk recorded m sig))

def findEnvForgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (simSign : Msg → Sig)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → Option (Msg × Sig)
  | .halt _ => none
  | .stepSign m next => findEnvForgery S pk simSign (m :: recorded) (next (simSign m))
  | .stepVerify m sig next =>
    if m ∉ recorded ∧ S.verify pk m sig = true then
      some (m, sig)
    else
      findEnvForgery S pk simSign recorded (next (idealSigVerify S pk recorded m sig))

theorem execReal_eq_execIdeal_unless_forgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hSim : ∀ m, simSign m = S.sign sk m)
    (recorded : List Msg) :
    ∀ (Z : UcSigEnv PK Msg Sig),
      findEnvForgery S pk simSign recorded Z = none →
      execRealSig S pk sk Z = execIdealSig S pk simSign recorded Z
  | .halt _, _ => rfl
  | .stepSign m next, hNone => by
    simp only [findEnvForgery] at hNone
    simp only [execRealSig, execIdealSig, ← hSim m]
    exact execReal_eq_execIdeal_unless_forgery S pk sk simSign hSim (m :: recorded) (next (simSign m)) hNone
  | .stepVerify m sig next, hNone => by
    simp only [findEnvForgery] at hNone
    by_cases hBad : m ∉ recorded ∧ S.verify pk m sig = true
    · simp [hBad] at hNone
    · simp only [hBad, ↓reduceIte] at hNone
      have hVerdictEq : S.verify pk m sig = idealSigVerify S pk recorded m sig := by
        unfold idealSigVerify
        by_cases hm : m ∈ recorded
        · simp [hm]
        · cases hv : S.verify pk m sig
          · simp [hm]
          · exact False.elim (hBad ⟨hm, hv⟩)
      simp only [execRealSig, execIdealSig, hVerdictEq]
      exact execReal_eq_execIdeal_unless_forgery S pk sk simSign hSim recorded
        (next (idealSigVerify S pk recorded m sig)) hNone

def signedBeforeForgery {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (simSign : Msg → Sig)
    (recorded : List Msg) : UcSigEnv PK Msg Sig → List Msg
  | .halt _ => recorded
  | .stepSign m next => signedBeforeForgery S pk simSign (m :: recorded) (next (simSign m))
  | .stepVerify m sig next =>
    if m ∉ recorded ∧ S.verify pk m sig = true then
      recorded
    else
      signedBeforeForgery S pk simSign recorded (next (idealSigVerify S pk recorded m sig))

theorem findEnvForgery_sound {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (simSign : Msg → Sig)
    (recorded : List Msg) :
    ∀ (Z : UcSigEnv PK Msg Sig) {mStar : Msg} {sigStar : Sig},
      findEnvForgery S pk simSign recorded Z = some (mStar, sigStar) →
      mStar ∉ signedBeforeForgery S pk simSign recorded Z ∧ S.verify pk mStar sigStar = true
  | .halt _, _, _, h => by cases h
  | .stepSign m next, _, _, h => by
    simp only [findEnvForgery] at h
    simp only [signedBeforeForgery]
    exact findEnvForgery_sound S pk simSign (m :: recorded) (next (simSign m)) h
  | .stepVerify m sig next, _, _, h => by
    simp only [findEnvForgery] at h
    simp only [signedBeforeForgery]
    by_cases hBad : m ∉ recorded ∧ S.verify pk m sig = true
    · simp only [hBad] at h ⊢
      injection h with hPair
      injection hPair with hm hs
      subst hm hs
      exact hBad
    · simp only [hBad] at h ⊢
      exact findEnvForgery_sound S pk simSign recorded (next (idealSigVerify S pk recorded m sig)) h

@[expose] def UcIndistinguishableOn {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (Z : UcSigEnv PK Msg Sig) : Prop :=
  execRealSig S pk sk Z = execIdealSig S pk simSign [] Z

/-- **Canetti UC Signature Equivalence (`ucRealizes_iff_eufCma`)**:
For any EUF-CMA signing oracle / simulator callback `simSign : Msg → Sig` agreeing with `S.sign sk`
on queried messages (without `execIdealSig` ever holding `sk`), distinguishing `Real` from `Ideal`
constructively extracts a fresh EUF-CMA forgery `(mStar, sigStar)`. -/
theorem ucRealizes_iff_eufCma {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hSim : ∀ m, simSign m = S.sign sk m) :
    (∀ Z : UcSigEnv PK Msg Sig,
      ¬ UcIndistinguishableOn S pk sk simSign Z →
      ∃ mStar sigStar,
        findEnvForgery S pk simSign [] Z = some (mStar, sigStar) ∧
        mStar ∉ signedBeforeForgery S pk simSign [] Z ∧
        S.verify pk mStar sigStar = true) ∧
    (∀ mStar sigStar, S.verify pk mStar sigStar = true →
      ¬ UcIndistinguishableOn S pk sk simSign (.stepVerify mStar sigStar (fun b => .halt b))) := by
  refine ⟨?_, ?_⟩
  · intro Z hDist
    cases hFind : findEnvForgery S pk simSign [] Z with
    | none =>
      exact False.elim (hDist (execReal_eq_execIdeal_unless_forgery S pk sk simSign hSim [] Z hFind))
    | some pair =>
      rcases pair with ⟨mStar, sigStar⟩
      obtain ⟨hFresh, hVer⟩ := findEnvForgery_sound S pk simSign [] Z hFind
      exact ⟨mStar, sigStar, rfl, hFresh, hVer⟩
  · intro mStar sigStar hVer hEq
    have hReal : execRealSig S pk sk (.stepVerify mStar sigStar (fun b => .halt b)) = true := by
      simp [execRealSig, hVer]
    have hIdeal : execIdealSig S pk simSign [] (.stepVerify mStar sigStar (fun b => .halt b)) = false := by
      simp [execIdealSig, idealSigVerify]
    have hEq' : execRealSig S pk sk (.stepVerify mStar sigStar (fun b => .halt b)) =
        execIdealSig S pk simSign [] (.stepVerify mStar sigStar (fun b => .halt b)) := hEq
    rw [hReal, hIdeal] at hEq'
    cases hEq'

def execMultiRealSig {PK SK Msg Sig : Type}
    (S_sig : AbstractSigScheme PK SK Msg Sig) : List (PK × SK × UcSigEnv PK Msg Sig) → List Bool
  | [] => []
  | (pk, sk, Z) :: rest => execRealSig S_sig pk sk Z :: execMultiRealSig S_sig rest

/-- Ideal multi-session execution takes only public `(pk, simSign, Z)` triples — ZERO `sk : SK`! -/
def execMultiIdealSig {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S_sig : AbstractSigScheme PK SK Msg Sig) : List (PK × (Msg → Sig) × UcSigEnv PK Msg Sig) → List Bool
  | [] => []
  | (pk, simSign, Z) :: rest => execIdealSig S_sig pk simSign [] Z :: execMultiIdealSig S_sig rest

theorem multi_session_uc_realizes {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S_sig : AbstractSigScheme PK SK Msg Sig) :
    (∀ (sessions : List (PK × SK × (Msg → Sig) × UcSigEnv PK Msg Sig)),
      (∀ pk sk simSign Z, (pk, sk, simSign, Z) ∈ sessions → ∀ m, simSign m = S_sig.sign sk m) →
      execMultiRealSig S_sig (sessions.map (fun (pk, sk, _, Z) => (pk, sk, Z))) =
        execMultiIdealSig S_sig (sessions.map (fun (pk, _, simSign, Z) => (pk, simSign, Z))) ∨
      ∃ pk sk simSign Z mStar sigStar,
        (pk, sk, simSign, Z) ∈ sessions ∧
        mStar ∉ signedBeforeForgery S_sig pk simSign [] Z ∧
        S_sig.verify pk mStar sigStar = true) ∧
    (∀ (S eps : Nat) (score : Nat → Nat),
      (∀ i, i < S → natAbsDiff (score i) (score (i + 1)) ≤ eps) →
      natAbsDiff (score 0) (score S) ≤ S * eps) := by
  refine ⟨?_, ?_⟩
  · intro sessions hAllSim
    induction sessions with
    | nil => exact .inl rfl
    | cons hd rest ih =>
      rcases hd with ⟨pk, sk, simSign, Z⟩
      have hHeadSim : ∀ m, simSign m = S_sig.sign sk m := hAllSim pk sk simSign Z (.head _)
      have hRestSim : ∀ pk' sk' sim' Z', (pk', sk', sim', Z') ∈ rest → ∀ m, sim' m = S_sig.sign sk' m :=
        fun pk' sk' sim' Z' hm => hAllSim pk' sk' sim' Z' (.tail _ hm)
      by_cases hHead : execRealSig S_sig pk sk Z = execIdealSig S_sig pk simSign [] Z
      · rcases ih hRestSim with hRestEq | ⟨pk', sk', sim', Z', mStar, sigStar, hMem, hFresh, hVer⟩
        · exact .inl (by simp [execMultiRealSig, execMultiIdealSig, hHead, hRestEq])
        · exact .inr ⟨pk', sk', sim', Z', mStar, sigStar, .tail _ hMem, hFresh, hVer⟩
      · obtain ⟨mStar, sigStar, _, hFresh, hVer⟩ := (ucRealizes_iff_eufCma S_sig pk sk simSign hHeadSim).1 Z hHead
        exact .inr ⟨pk, sk, simSign, Z, mStar, sigStar, .head _, hFresh, hVer⟩
  · intro S eps score hStep
    induction S with
    | zero => simp [natAbsDiff]
    | succ s ih =>
      have ih' := ih (fun i hi => hStep i (Nat.lt_succ_of_lt hi))
      have hLast := hStep s (Nat.lt_succ_self s)
      have hTri := natAbsDiff_triangle (score 0) (score s) (score (s + 1))
      have hLe := Nat.le_trans hTri (Nat.add_le_add ih' hLast)
      rwa [Nat.succ_mul]

structure CallingProtocol (HighIn HighOut PK Msg Sig : Type) where
  compileEnv : (HighIn → HighOut → Bool) → HighIn → UcSigEnv PK Msg Sig

theorem uc_composition_theorem {HighIn HighOut PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (pk : PK) (sk : SK) (simSign : Msg → Sig)
    (hSim : ∀ m, simSign m = S.sign sk m)
    (ρ : CallingProtocol HighIn HighOut PK Msg Sig)
    (inp : HighIn) (post : HighIn → HighOut → Bool) :
    let Z := ρ.compileEnv post inp
    execRealSig S pk sk Z = execIdealSig S pk simSign [] Z ∨
    (∃ mStar sigStar,
      mStar ∉ signedBeforeForgery S pk simSign [] Z ∧
      S.verify pk mStar sigStar = true) := by
  intro Z
  by_cases hEq : execRealSig S pk sk Z = execIdealSig S pk simSign [] Z
  · exact .inl hEq
  · obtain ⟨mStar, sigStar, _, hFresh, hVer⟩ := (ucRealizes_iff_eufCma S pk sk simSign hSim).1 Z hEq
    exact .inr ⟨mStar, sigStar, hFresh, hVer⟩

/-! ## 4. Finite Sample Spaces: Fubini, Bijection Invariance, Preprocessing-Generator Games -/

theorem finSum_mul_left {n : Nat} (c : Nat) (f : Fin n → Nat) :
    finSum n (fun i => c * f i) = c * finSum n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hIh := ih (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    simp only [finSum]
    rw [hIh, Nat.mul_add]

/-- Exchange of two finite sums. -/
theorem finSum_comm {n m : Nat} (F : Fin n → Fin m → Nat) :
    finSum n (fun i => finSum m (fun j => F i j)) = finSum m (fun j => finSum n (fun i => F i j)) := by
  induction n with
  | zero =>
    have h : finSum m (fun j => finSum 0 (fun i => F i j)) = finSum m (fun _ => 0) :=
      finSum_congr (fun _ => rfl)
    rw [h, finSum_const]
    rfl
  | succ n ih =>
    have hIh := ih (fun i j => F ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j)
    simp only [finSum]
    rw [hIh]
    exact (finSum_add (fun j => F ⟨0, Nat.zero_lt_succ n⟩ j)
      (fun j => finSum n (fun i => F ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j))).symm

theorem finSum_ite_eq {n : Nat} (a : Fin n) (g : Fin n → Nat) :
    finSum n (fun j => if j = a then g j else 0) = g a := by
  have h : finSum n (fun j => if j = a then g j else 0) =
      finSum n (fun j => g a * (if j = a then 1 else 0)) := by
    apply finSum_congr
    intro j
    by_cases hj : j = a
    · rw [ite_eq_left hj, ite_eq_left hj, Nat.mul_one, hj]
    · rw [ite_eq_right hj, ite_eq_right hj, Nat.mul_zero]
  rw [h, finSum_mul_left, finSum_eq_indicator, Nat.mul_one]

/-- A finite sum is invariant under a permutation of its index set. -/
theorem finSum_perm_invariant {n : Nat} (π πinv : Fin n → Fin n)
    (hLeft : ∀ i, πinv (π i) = i) (hRight : ∀ j, π (πinv j) = j) (g : Fin n → Nat) :
    finSum n (fun i => g (π i)) = finSum n g := by
  have h1 : finSum n (fun i => g (π i)) =
      finSum n (fun i => finSum n (fun j => if j = π i then g j else 0)) :=
    finSum_congr (fun i => (finSum_ite_eq (π i) g).symm)
  have h2 : ∀ j : Fin n, finSum n (fun i => if j = π i then g j else 0) = g j := by
    intro j
    have h3 : finSum n (fun i => if j = π i then g j else 0) =
        finSum n (fun i => g j * (if i = πinv j then 1 else 0)) := by
      apply finSum_congr
      intro i
      by_cases hi : i = πinv j
      · have hj : j = π i := by rw [hi, hRight]
        rw [ite_eq_left hj, ite_eq_left hi, Nat.mul_one]
      · have hj : ¬ j = π i := fun h => hi (by rw [h, hLeft])
        rw [ite_eq_right hj, ite_eq_right hi, Nat.mul_zero]
    rw [h3, finSum_mul_left, finSum_eq_indicator, Nat.mul_one]
  exact h1.trans ((finSum_comm (fun i j => if j = π i then g j else 0)).trans (finSum_congr h2))

/-- **Uniform-Distribution Bijection Invariance (`finSum_bijection_invariant`)**: over a sample
    space `Ω` enumerated by `enum`, pre-composing any weight `g` with a bijection `e` of `Ω`
    leaves the total weight unchanged. -/
theorem finSum_bijection_invariant {Ω : Type} {C : Nat}
    (enum : SimpleEquiv (Fin C) Ω) (e : SimpleEquiv Ω Ω) (g : Ω → Nat) :
    finSum C (fun i => g (e.toFun (enum.toFun i))) = finSum C (fun i => g (enum.toFun i)) := by
  have h := finSum_perm_invariant
    (fun i => enum.invFun (e.toFun (enum.toFun i)))
    (fun j => enum.invFun (e.invFun (enum.toFun j)))
    (fun i => by simp only [enum.right_inv, e.left_inv, enum.left_inv])
    (fun j => by simp only [enum.right_inv, e.right_inv, enum.left_inv])
    (fun i => g (enum.toFun i))
  simp only [enum.right_inv] at h
  exact h

theorem finSum_indicator_or_le {n : Nat} (p q : Fin n → Bool) :
    finSum n (fun i => if (p i || q i) then 1 else 0) ≤
      finSum n (fun i => if p i then 1 else 0) + finSum n (fun i => if q i then 1 else 0) := by
  have h : ∀ i : Fin n, (if (p i || q i) then 1 else 0) ≤
      (if p i then 1 else 0) + (if q i then 1 else 0) := by
    intro i
    cases p i <;> cases q i <;> decide
  exact Nat.le_trans (finSum_le_finSum h)
    (Nat.le_of_eq (finSum_add (fun i => if p i then 1 else 0) (fun i => if q i then 1 else 0)))

/-- At most one index satisfies a predicate whose satisfying indices all coincide. -/
theorem finSum_indicator_le_one_of_unique : ∀ (n : Nat) (p : Fin n → Bool),
    (∀ i j : Fin n, p i = true → p j = true → i = j) →
    finSum n (fun i => if p i then 1 else 0) ≤ 1
  | 0, _, _ => Nat.zero_le 1
  | n + 1, p, hUniq => by
    simp only [finSum]
    cases hp0 : p ⟨0, Nat.zero_lt_succ n⟩ with
    | true =>
      have hRest : finSum n (fun i => if p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) =
          finSum n (fun _ => 0) := by
        apply finSum_congr
        intro i
        have hpi : p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = false := by
          cases hpi : p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ with
          | false => rfl
          | true =>
            exact absurd (congrArg Fin.val (hUniq _ _ hp0 hpi)) (Nat.succ_ne_zero i.1).symm
        simp only [hpi, Bool.false_eq_true, ↓reduceIte]
      rw [hRest, finSum_const]
      simp
    | false =>
      have ih := finSum_indicator_le_one_of_unique n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        (fun i j hi hj => Fin.ext (Nat.succ.inj (congrArg Fin.val (hUniq _ _ hi hj))))
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih

theorem natAbsDiff_add_le (a b c d : Nat) :
    natAbsDiff (a + b) (c + d) ≤ natAbsDiff a c + natAbsDiff b d := by
  unfold natAbsDiff
  split <;> split <;> split <;> omega

theorem natAbsDiff_finSum_le {n : Nat} (f g : Fin n → Nat) :
    natAbsDiff (finSum n f) (finSum n g) ≤ finSum n (fun i => natAbsDiff (f i) (g i)) := by
  induction n with
  | zero => exact Nat.le_of_eq rfl
  | succ n ih =>
    simp only [finSum]
    exact Nat.le_trans (natAbsDiff_add_le _ _ _ _) (Nat.add_le_add_left (ih _ _) _)

theorem natAbsDiff_mul_left (c a b : Nat) : natAbsDiff (c * a) (c * b) = c * natAbsDiff a b := by
  unfold natAbsDiff
  by_cases h : a ≤ b
  · rw [ite_eq_left h, ite_eq_left (Nat.mul_le_mul_left c h), Nat.mul_sub]
  · have hba : b ≤ a := Nat.le_of_lt (Nat.gt_of_not_le h)
    have h' : c * b ≤ c * a := Nat.mul_le_mul_left c hba
    rw [ite_eq_right h, Nat.mul_sub]
    split
    · omega
    · rfl

/-- Number of accepting sample pairs of a Boolean experiment `X` over two independent uniformly
    indexed sample spaces (`Ca * Cb` pairs in total). -/
@[expose] def acceptPairs {A B : Type} (Ca Cb : Nat) (sa : Fin Ca → A) (sb : Fin Cb → B)
    (X : A → B → Bool) : Nat :=
  finSum Ca (fun i => finSum Cb (fun j => if X (sa i) (sb j) then 1 else 0))

/-- Generator-indistinguishability game. `gen` maps a uniform seed in `Fin Cg` to a sample; `unif`
    indexes the reference sample space; `B x` is the number of internal coin values on which the
    (randomised) distinguisher accepts `x`. The value is the advantage numerator
    `|Pr[B(gen s)] - Pr[B(unif u)]|` cleared of the two sample-space sizes `Cg` and `Cu`. -/
@[expose] def samplerAdvNum {X : Type} (Cg Cu : Nat) (gen : Fin Cg → X) (unif : Fin Cu → X)
    (B : X → Nat) : Nat :=
  natAbsDiff (finSum Cg (fun s => B (gen s)) * Cu) (finSum Cu (fun u => B (unif u)) * Cg)

/-- PRG game for an experiment `X`: the reduction replaces the pad tape expanded from a seed by
    `prg` with a uniform tape, drawing the second component from `ot` itself. -/
@[expose] def prgReductionAdvNum {T K : Type} (Cs Ct Co : Nat) (prg : Fin Cs → T)
    (unifT : Fin Ct → T) (ot : Fin Co → K) (X : T → K → Bool) : Nat :=
  samplerAdvNum Cs Ct prg unifT (fun τ => finSum Co (fun o => if X τ (ot o) then 1 else 0))

/-- Correlated-key (OT) game for an experiment `X`: the reduction replaces the key produced by the
    correlation generator `ot` with a uniform key, drawing the tape uniformly itself. -/
@[expose] def otReductionAdvNum {T K : Type} (Ct Co CK : Nat) (unifT : Fin Ct → T)
    (ot : Fin Co → K) (unifK : Fin CK → K) (X : T → K → Bool) : Nat :=
  samplerAdvNum Co CK ot unifK (fun κ => finSum Ct (fun i => if X (unifT i) κ then 1 else 0))

theorem samplerAdvNum_self {X : Type} (C : Nat) (gen : Fin C → X) (B : X → Nat) :
    samplerAdvNum C C gen gen B = 0 := by
  unfold samplerAdvNum natAbsDiff
  split <;> omega

/-- The game is not vacuous: a constant generator is told apart from a two-point space. -/
theorem samplerAdvNum_constant_generator_detected :
    samplerAdvNum 1 2 (fun _ => false) (fun i => decide (i.val = 1)) (fun b => if b then 1 else 0) = 1 := by
  decide

private theorem natAbsDiff_three_hop (N0 N1 N2 N3 Cs Co Ct CK G : Nat)
    (h : natAbsDiff N2 N3 ≤ G) :
    natAbsDiff (N0 * (Ct * CK)) (N3 * (Cs * Co)) ≤
      Cs * Co * G + CK * natAbsDiff (N0 * Ct) (N1 * Cs) + Cs * natAbsDiff (N1 * CK) (N2 * Co) := by
  have e0 : N0 * (Ct * CK) = CK * (N0 * Ct) := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have e1 : CK * (N1 * Cs) = Cs * (N1 * CK) := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have e2 : Cs * (N2 * Co) = Cs * Co * N2 := by
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  have e3 : N3 * (Cs * Co) = Cs * Co * N3 := by
    simp only [Nat.mul_comm]
  have hA : natAbsDiff (CK * (N0 * Ct)) (CK * (N1 * Cs)) = CK * natAbsDiff (N0 * Ct) (N1 * Cs) :=
    natAbsDiff_mul_left _ _ _
  have hB : natAbsDiff (CK * (N1 * Cs)) (Cs * Co * N2) = Cs * natAbsDiff (N1 * CK) (N2 * Co) := by
    rw [e1, ← e2]
    exact natAbsDiff_mul_left _ _ _
  have hC : natAbsDiff (Cs * Co * N2) (Cs * Co * N3) ≤ Cs * Co * G := by
    rw [natAbsDiff_mul_left]
    exact Nat.mul_le_mul_left _ h
  have t1 := natAbsDiff_triangle (CK * (N0 * Ct)) (CK * (N1 * Cs)) (Cs * Co * N3)
  have t2 := natAbsDiff_triangle (CK * (N1 * Cs)) (Cs * Co * N2) (Cs * Co * N3)
  rw [hA] at t1
  rw [hB] at t2
  rw [e0, e3]
  omega

/-- **Simulation-up-to-Bad Counting Hop (`acceptPairs_gap_of_bijection`)**: if a tape bijection
    `e` makes experiment `X` on `τ` equal to experiment `Y` on `e τ` outside a bad event, and for
    every tape at most `q` keys are bad, then over uniform tape and key the two experiments differ
    on at most `Ct * q` sample pairs. -/
theorem acceptPairs_gap_of_bijection {T K : Type} {Ct CK : Nat}
    (enumT : SimpleEquiv (Fin Ct) T) (e : SimpleEquiv T T) (unifK : Fin CK → K)
    (X Y : T → K → Bool) (bad : T → K → Bool) (q : Nat)
    (hAgree : ∀ τ κ, bad τ κ = false → X τ κ = Y (e.toFun τ) κ)
    (hBad : ∀ τ, finSum CK (fun j => if bad τ (unifK j) then 1 else 0) ≤ q) :
    natAbsDiff (acceptPairs Ct CK enumT.toFun unifK X) (acceptPairs Ct CK enumT.toFun unifK Y) ≤
      Ct * q := by
  have hInv := finSum_bijection_invariant enumT e
    (fun τ => finSum CK (fun j => if Y τ (unifK j) then 1 else 0))
  have hPt : ∀ i : Fin Ct,
      natAbsDiff (finSum CK (fun j => if X (enumT.toFun i) (unifK j) then 1 else 0))
                 (finSum CK (fun j => if Y (e.toFun (enumT.toFun i)) (unifK j) then 1 else 0)) ≤ q :=
    fun i => Nat.le_trans
      (finSum_indicator_diff_le (fun j => X (enumT.toFun i) (unifK j))
        (fun j => Y (e.toFun (enumT.toFun i)) (unifK j))
        (fun j => bad (enumT.toFun i) (unifK j)) (fun j hj => hAgree _ _ hj))
      (hBad (enumT.toFun i))
  have hSum := natAbsDiff_finSum_le
    (fun i : Fin Ct => finSum CK (fun j => if X (enumT.toFun i) (unifK j) then 1 else 0))
    (fun i : Fin Ct => finSum CK (fun j => if Y (e.toFun (enumT.toFun i)) (unifK j) then 1 else 0))
  have hBound := finSum_le_finSum (g := fun _ : Fin Ct => q) hPt
  rw [finSum_const] at hBound
  rw [hInv] at hSum
  exact Nat.le_trans hSum hBound

/-- **Preprocessing Hybrid Reduction (`preprocessing_hybrid_bound`)**: let `X` be the real
    experiment and `Y` the ideal one. If over uniform tape and uniform key they differ on at most
    `G` sample pairs, then running `X` on `prg`-expanded tapes and `ot`-generated keys differs from
    `Y` on uniform samples by at most the uniform gap plus the advantages of the two explicit
    reduction distinguishers, all over the common denominator `Cs * Co * Ct * CK`. -/
theorem preprocessing_hybrid_bound {T K : Type} (Cs Ct Co CK : Nat)
    (prg : Fin Cs → T) (unifT : Fin Ct → T) (ot : Fin Co → K) (unifK : Fin CK → K)
    (X Y : T → K → Bool) (G : Nat)
    (hGap : natAbsDiff (acceptPairs Ct CK unifT unifK X) (acceptPairs Ct CK unifT unifK Y) ≤ G) :
    natAbsDiff (acceptPairs Cs Co prg ot X * (Ct * CK))
               (acceptPairs Ct CK unifT unifK Y * (Cs * Co)) ≤
      Cs * Co * G
        + CK * prgReductionAdvNum Cs Ct Co prg unifT ot X
        + Cs * otReductionAdvNum Ct Co CK unifT ot unifK X := by
  have hOt1 : finSum Co (fun o => finSum Ct (fun i => if X (unifT i) (ot o) then 1 else 0)) =
      acceptPairs Ct Co unifT ot X :=
    finSum_comm (fun (o : Fin Co) (i : Fin Ct) => if X (unifT i) (ot o) then 1 else 0)
  have hOt2 : finSum CK (fun u => finSum Ct (fun i => if X (unifT i) (unifK u) then 1 else 0)) =
      acceptPairs Ct CK unifT unifK X :=
    finSum_comm (fun (u : Fin CK) (i : Fin Ct) => if X (unifT i) (unifK u) then 1 else 0)
  have hPrg : prgReductionAdvNum Cs Ct Co prg unifT ot X =
      natAbsDiff (acceptPairs Cs Co prg ot X * Ct) (acceptPairs Ct Co unifT ot X * Cs) := rfl
  have hOt : otReductionAdvNum Ct Co CK unifT ot unifK X =
      natAbsDiff (acceptPairs Ct Co unifT ot X * CK) (acceptPairs Ct CK unifT unifK X * Co) := by
    show natAbsDiff
        (finSum Co (fun o => finSum Ct (fun i => if X (unifT i) (ot o) then 1 else 0)) * CK)
        (finSum CK (fun u => finSum Ct (fun i => if X (unifT i) (unifK u) then 1 else 0)) * Co) = _
    rw [hOt1, hOt2]
  rw [hPrg, hOt]
  exact natAbsDiff_three_hop _ _ _ _ Cs Co Ct CK G hGap

/-- Break witness: an advantage above the uniform gap forces one of the two generator games to
    have non-zero advantage for the explicit reduction distinguisher. -/
theorem preprocessing_break_witness {T K : Type} (Cs Ct Co CK : Nat)
    (prg : Fin Cs → T) (unifT : Fin Ct → T) (ot : Fin Co → K) (unifK : Fin CK → K)
    (X Y : T → K → Bool) (G : Nat)
    (hGap : natAbsDiff (acceptPairs Ct CK unifT unifK X) (acceptPairs Ct CK unifT unifK Y) ≤ G)
    (hDist : Cs * Co * G < natAbsDiff (acceptPairs Cs Co prg ot X * (Ct * CK))
                                       (acceptPairs Ct CK unifT unifK Y * (Cs * Co))) :
    0 < prgReductionAdvNum Cs Ct Co prg unifT ot X ∨
    0 < otReductionAdvNum Ct Co CK unifT ot unifK X := by
  have hB := preprocessing_hybrid_bound Cs Ct Co CK prg unifT ot unifK X Y G hGap
  cases hp : prgReductionAdvNum Cs Ct Co prg unifT ot X with
  | succ a => exact .inl (Nat.succ_pos a)
  | zero =>
    cases ho : otReductionAdvNum Ct Co CK unifT ot unifK X with
    | succ b => exact .inr (Nat.succ_pos b)
    | zero =>
      rw [hp, ho, Nat.mul_zero, Nat.mul_zero] at hB
      exact absurd hDist (Nat.not_lt.mpr hB)

/-! ## 5. Shamir Share / Pad Rebalancing for Masked Openings -/

section ShareRebalance
open CommRingOps

theorem vanishCorruptUnit0_length {R : Type} [CommRingOps R] (inv : R → R) (t : Nat)
    (corruptPts : List R) (hCard : corruptPts.length + 1 ≤ t) :
    (vanishCorruptUnit0 inv t corruptPts).length = t := by
  unfold vanishCorruptUnit0
  dsimp only
  rw [List.length_append, List.length_replicate, vanishCorruptRaw_length]
  omega

private theorem sub_add_add_cancel_left {R : Type} [LawfulCommRing R] (w p q : R) :
    sub (add w p) (add w q) = sub p q := by
  have h : add w p = add (sub p q) (add w q) := by
    rw [LawfulCommRing.add_comm w q, ← LawfulCommRing.add_assoc, sub_add_cancel_right,
        LawfulCommRing.add_comm]
  rw [h, add_sub_cancel_right]

/-- Bijection on the sharing randomness of a degree-`d` Shamir sharing `w :: A` that turns a
    sharing of `w` into a sharing of `zero` with the same shares at every corrupt point. -/
def shamirShare_rebalanceEquiv {R : Type} [LawfulCommRing R]
    (inv : R → R) (d : Nat) (corruptPts : List R)
    (w : R) (hCard : corruptPts.length + 1 ≤ d + 1) :
    SimpleEquiv (ShamirPadPoly R d) (ShamirPadPoly R d) :=
  let delta := polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts).tail
  have hDeltaLen : delta.length = d := by
    rw [polyScale_length, List.length_tail, vanishCorruptUnit0_length inv (d + 1) corruptPts hCard]
    exact Nat.add_sub_cancel d 1
  { toFun := fun ⟨p, hp⟩ => ⟨polySubFixed p delta, by rw [polySubFixed_length p delta (hp.trans hDeltaLen.symm), hp]⟩
    invFun := fun ⟨q, hq⟩ => ⟨polyAddFixed q delta, by rw [polyAddFixed_length q delta (hq.trans hDeltaLen.symm), hq]⟩
    left_inv := fun ⟨p, hp⟩ => Subtype.ext (polyAdd_polySub_cancel p delta (hp.trans hDeltaLen.symm))
    right_inv := fun ⟨q, hq⟩ => Subtype.ext (polySub_polyAdd_cancel q delta (hq.trans hDeltaLen.symm)) }

/-- **Masked-Opening Rebalancing (`shamir_share_pad_rebalance`)**: for a secret `w` shared by the
    standard polynomial `w :: A` and masked by the pad polynomial `P`, moving `A` and `P` through
    the two bijections yields a sharing `zero :: A'` of `zero` and a pad `P'` such that every
    corrupt party's share and pad share are unchanged and the masked polynomial `(w :: A) + P`
    takes the same value at every point (so every broadcast masked share is unchanged). -/
theorem shamir_share_pad_rebalance {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (d : Nat) (corruptPts : List R) (w : R)
    (hCard : corruptPts.length + 1 ≤ d + 1)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero)
    (A : ShamirPadPoly R d) (P : ShamirPadPoly R (d + 1)) :
    let A' := (shamirShare_rebalanceEquiv inv d corruptPts w hCard).toFun A
    let P' := (shamir_rebalanceEquiv inv (d + 1) corruptPts w hCard).toFun P
    (∀ xc ∈ corruptPts,
      RoundPoly.evalCoeffs (zero :: A'.1) xc = RoundPoly.evalCoeffs (w :: A.1) xc) ∧
    (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs P'.1 xc = RoundPoly.evalCoeffs P.1 xc) ∧
    (∀ x : R,
      add (RoundPoly.evalCoeffs (zero :: A'.1) x) (RoundPoly.evalCoeffs P'.1 x) =
        add (RoundPoly.evalCoeffs (w :: A.1) x) (RoundPoly.evalCoeffs P.1 x)) := by
  intro A' P'
  obtain ⟨hULen, hU0, hUCorr⟩ := vanishCorruptUnit0_props inv hInv hCard hNonZero
  obtain ⟨_, hPadShares⟩ :=
    pad_bijection_masked_openings_uniform inv hInv (d + 1) corruptPts w hCard hNonZero P
  have hScaleLen : (polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts)).length = d + 1 := by
    rw [polyScale_length, hULen]
  have hP' : ∀ x : R, RoundPoly.evalCoeffs P'.1 x =
      add (RoundPoly.evalCoeffs P.1 x)
          (mul w (RoundPoly.evalCoeffs (vanishCorruptUnit0 inv (d + 1) corruptPts) x)) := by
    intro x
    change RoundPoly.evalCoeffs
      (polyAddFixed P.1 (polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts))) x = _
    rw [evalCoeffs_addFixed P.1 _ _ (P.2.trans hScaleLen.symm), evalCoeffs_scale]
  have hUCons : vanishCorruptUnit0 inv (d + 1) corruptPts =
      one :: (vanishCorruptUnit0 inv (d + 1) corruptPts).tail := by
    cases hU : vanishCorruptUnit0 inv (d + 1) corruptPts with
    | nil =>
      rw [hU] at hULen
      exact absurd hULen (Nat.succ_ne_zero d).symm
    | cons c cs =>
      rw [hU] at hU0
      have hc : c = one := by
        simpa only [RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
          using hU0
      rw [hc]
      rfl
  have hTailLen : (vanishCorruptUnit0 inv (d + 1) corruptPts).tail.length = d := by
    rw [List.length_tail, hULen]
    exact Nat.add_sub_cancel d 1
  have hA' : ∀ x : R, RoundPoly.evalCoeffs (zero :: A'.1) x =
      sub (RoundPoly.evalCoeffs (w :: A.1) x)
          (mul w (RoundPoly.evalCoeffs (vanishCorruptUnit0 inv (d + 1) corruptPts) x)) := by
    intro x
    have hEvalU : RoundPoly.evalCoeffs (vanishCorruptUnit0 inv (d + 1) corruptPts) x =
        add one (mul x (RoundPoly.evalCoeffs (vanishCorruptUnit0 inv (d + 1) corruptPts).tail x)) :=
      congrArg (fun l => RoundPoly.evalCoeffs l x) hUCons
    have hLenEq : A.1.length =
        (polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts).tail).length := by
      rw [polyScale_length, hTailLen, A.2]
    change RoundPoly.evalCoeffs
      (zero :: polySubFixed A.1 (polyScale w (vanishCorruptUnit0 inv (d + 1) corruptPts).tail)) x = _
    rw [hEvalU]
    simp only [RoundPoly.evalCoeffs_cons]
    rw [evalCoeffs_subFixed A.1 _ x hLenEq, evalCoeffs_scale, LawfulCommRing.zero_add,
        LawfulCommRing.mul_sub, LawfulCommRing.left_distrib w, LawfulCommRing.mul_one,
        sub_add_add_cancel_left, ← LawfulCommRing.mul_assoc x w, LawfulCommRing.mul_comm x w,
        LawfulCommRing.mul_assoc w x]
  refine ⟨?_, hPadShares, ?_⟩
  · intro xc hxc
    rw [hA' xc, hUCorr xc hxc, LawfulCommRing.mul_zero, LawfulCommRing.sub_zero]
  · intro x
    rw [hA' x, hP' x, LawfulCommRing.add_comm (RoundPoly.evalCoeffs P.1 x),
        ← LawfulCommRing.add_assoc, sub_add_cancel_right]

/-- Inhabitedness over `GF(4)`: degree bound `d = 1`, one corrupt point, a non-zero secret. -/
theorem shamir_share_pad_rebalance_gf4
    (A : ShamirPadPoly (TowerElem 1) 1) (P : ShamirPadPoly (TowerElem 1) 2) :
    let A' := (shamirShare_rebalanceEquiv (towerInv 1) 1 [(towerOne 1)]
      (towerOne 1) (by decide)).toFun A
    let P' := (shamir_rebalanceEquiv (towerInv 1) 2 [(towerOne 1)]
      (towerOne 1) (by decide)).toFun P
    RoundPoly.evalCoeffs (zero :: A'.1) (towerOne 1) =
      RoundPoly.evalCoeffs ((towerOne 1) :: A.1) (towerOne 1) ∧
    RoundPoly.evalCoeffs P'.1 (towerOne 1) =
      RoundPoly.evalCoeffs P.1 (towerOne 1) ∧
    (∀ x : TowerElem 1,
      add (RoundPoly.evalCoeffs (zero :: A'.1) x) (RoundPoly.evalCoeffs P'.1 x) =
        add (RoundPoly.evalCoeffs ((towerOne 1) :: A.1) x)
            (RoundPoly.evalCoeffs P.1 x)) := by
  intro A' P'
  have hNz : ∀ c ∈ [(towerOne 1)], c ≠ (zero : TowerElem 1) := by
    intro c hc
    rw [List.mem_singleton.mp hc]
    decide
  obtain ⟨h1, h2, h3⟩ :=
    shamir_share_pad_rebalance (towerInv 1) (towerMul_inv 1) 1 [(towerOne 1)]
      (towerOne 1) (by decide) hNz A P
  exact ⟨h1 _ (.head _), h2 _ (.head _), h3⟩

end ShareRebalance

end Qsag
end
